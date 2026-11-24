"""
avm2gml.py - SWF -> GameMaker project  (swflib reads, gmlib writes, as3_to_gml converts code).
 
Mapping
-------
    SWF shape (DefineShape*)   -> GM sprite (spr_shape_N)  + GM object (obj_shape_N)
    SWF sprite (DefineSprite)  -> GM object  obj_<LinkageClass>  (or obj_sprite_N when the
                                  clip has no class).  Create event spawns the children of
                                  the clip's first frame.
    SWF main-timeline frame    -> GM room (room_<label or frame_N>)
    SWF sound (DefineSound)    -> GM sound (snd_N);  StartSound on a frame -> room creation code
    ActionScript 3 class       -> the GM object of the same name, in its events:
                                    constructor / fields / methods ........ Create
                                    event listeners, timers, key events ... Step
                                    graphics.* / TextField drawing ........ Draw
                                  The document class becomes a persistent object that is
                                  placed in the first room.
 
Pipeline
--------
    1. swflib/FFDec : header, shapes (PNG+SVG), sounds, XML, AS3 scripts (.as)
    2. parse the XML into a model (shapes, sprites, timelines, symbol names)
    3. gmlib        : sprites, objects, rooms, instances, sounds
    4. as3_to_gml   : every .as class -> {Create, Step, Draw} -> gm.gm_add_event(...)
       (gmlib writes them to  <project>/objects/<obj>/Create_0.gml, Step_0.gml, Draw_0.gml)
 
Files needed side by side: avm2gml.py, gmlib.py, swflib.py, as3_to_gml.py
 
CLI:
    python avm2gml.py pb2.swf cha --java "C:\\Program Files\\Java\\jre1.8.0_503\\bin\\java.exe"
    python avm2gml.py pb2.swf cha --rooms-from sprite:12 --main Main
    python avm2gml.py pb2.swf cha --as3-dir my_as_files        # use .as files you already have
    python avm2gml.py pb2.swf cha --no-as3                     # graphics/rooms only
 
GUI / import:
    from avm2gml import run_pipeline
    yyp = run_pipeline("pb2.swf", "cha", log=print)
 
Nothing runs on import.
"""
 
import argparse
import math
import os
import re
import xml.etree.ElementTree as ET
 
import gmlib as gm
import swflib
import as2_to_gml as _a1g
 
DEFAULT_JAVA = swflib.DEFAULT_JAVA
DEFAULT_FFDEC = swflib.DEFAULT_FFDEC
 
PLACE_TAG_TYPES = ("PlaceObjectTag", "PlaceObject2Tag", "PlaceObject3Tag", "PlaceObject4Tag")
REMOVE_TAG_TYPES = ("RemoveObjectTag", "RemoveObject2Tag")
 
 
# ---------------------------------------------------------------------------
# SWF XML model (timelines are richer than swflib.read_placements)
# ---------------------------------------------------------------------------
 
def _f(value, default=0.0):
    try:
        return float(value)
    except (TypeError, ValueError):
        return default
 
 
def _parse_matrix(matrix):
    """(a, b, c, d, tx, ty) with x' = a*x + c*y + tx, y' = b*x + d*y + ty; tx/ty in pixels."""
    if matrix is None:
        return (1.0, 0.0, 0.0, 1.0, 0.0, 0.0)
 
    at = matrix.attrib
    tx = _f(at.get("translateX")) / 20.0
    ty = _f(at.get("translateY")) / 20.0
    has_scale = at.get("hasScale", "true") != "false"
    has_rotate = at.get("hasRotate", "true") != "false"
 
    a = _f(at.get("scaleX"), 1.0) if has_scale else 1.0
    d = _f(at.get("scaleY"), 1.0) if has_scale else 1.0
    b = _f(at.get("rotateSkew0")) if has_rotate else 0.0
    c = _f(at.get("rotateSkew1")) if has_rotate else 0.0
 
    if max(abs(a), abs(d)) >= 64:  # raw 16.16 fixed-point export
        a, d, b, c = (v / 65536.0 for v in (a, d, b, c))
    return (a, b, c, d, tx, ty)
 
 
def _parse_timeline(tags_element):
    """One dict per frame: {"label", "display": [placements by depth], "sounds": [ids]}."""
    frames = []
    if tags_element is None:
        return frames
 
    display, label, sounds = {}, None, []
    for tag in tags_element.findall("item"):
        tag_type = tag.attrib.get("type", "")
 
        if tag_type == "FrameLabelTag":
            label = tag.attrib.get("name") or label
 
        elif tag_type in PLACE_TAG_TYPES:
            depth = int(_f(tag.attrib.get("depth")))
            is_v1 = tag_type == "PlaceObjectTag"
            has_char = is_v1 or tag.attrib.get("placeFlagHasCharacter") == "true"
            is_move = tag.attrib.get("placeFlagMove") == "true"
            matrix_el = tag.find("matrix")
            if has_char and tag.attrib.get("characterId") is not None:
                display[depth] = {"charid": int(tag.attrib["characterId"]), "depth": depth,
                                  "m": _parse_matrix(matrix_el)}
            elif is_move and depth in display and matrix_el is not None:
                display[depth] = {**display[depth], "m": _parse_matrix(matrix_el)}
 
        elif tag_type in REMOVE_TAG_TYPES:
            display.pop(int(_f(tag.attrib.get("depth"))), None)
 
        elif tag_type == "StartSoundTag":
            if tag.attrib.get("soundId") is not None:
                sounds.append(int(tag.attrib["soundId"]))
 
        elif tag_type == "ShowFrameTag":
            frames.append({"label": label,
                           "display": [dict(display[k]) for k in sorted(display)],
                           "sounds": list(sounds)})
            label, sounds = None, []
    return frames
 
 
def _symbol_classes(root):
    """
    {character_id: class/export name} from SymbolClassTag + ExportAssetsTag.
    Unlike swflib._symbol_names this keeps id 0 - the document class of the main timeline.
    """
    names = {}
    for tag_type in ("SymbolClassTag", "ExportAssetsTag"):
        for tag in root.findall(f".//item[@type='{tag_type}']"):
            ids, labels = tag.find("tags"), tag.find("names")
            if ids is None or labels is None:
                continue
            for cid, label in zip(ids.findall("item"), labels.findall("item")):
                if cid.text and label.text and cid.text.strip().isdigit():
                    names.setdefault(int(cid.text.strip()), label.text.strip())
    return names
 
 
def parse_swf(xml_path):
    """
    Returns {"shapes":  {char_id: (xmin_px, ymin_px)},
             "sprites": {char_id: [frame, ...]},
             "symbols": {char_id: class name}      # id 0 = document class
             "main":    [frame, ...]}
    """
    root = ET.parse(xml_path).getroot()
 
    shapes = {}
    for item in swflib.read_shapes(xml_path)["items"]:
        shapes[item["id"]] = (item["x"], item["y"])
 
    sprites = {}
    for tag in root.findall(".//item[@type='DefineSpriteTag']"):
        sprite_id = tag.attrib.get("spriteId")
        if sprite_id is not None:
            sprites[int(sprite_id)] = _parse_timeline(tag.find("subTags"))
 
    main_tags = root.find("tags")
    main = _parse_timeline(main_tags if main_tags is not None else root)
    return {"shapes": shapes, "sprites": sprites, "symbols": _symbol_classes(root), "main": main}
 
 
# ---------------------------------------------------------------------------
# Naming / transform helpers
# ---------------------------------------------------------------------------
 
def _resource_name(prefix, value):
    return gm.gm_sanitize_name(f"{prefix}_{value}")
 
 
def _short_class(full_name):
    """'com.game.Player' / 'com.game::Player' -> 'Player'"""
    return re.split(r"[.:]+", full_name.strip())[-1]
 
 
def _unique_name(base_name, used):
    """
    A name not in `used`.  Comparison ignores case: on Windows objects/obj_Foo and
    objects/obj_foo are the SAME folder, so GameMaker cannot load both.  `used` holds
    lower-case names.
    """
    name, suffix = base_name, 2
    while name.lower() in used:
        name = f"{base_name}_{suffix}"
        suffix += 1
    used.add(name.lower())
    return name
 
 
# ---- scaleX / scaleY variables + real sound names ----------------------------
SCALE_SYNC = "scaleX = image_xscale;\nscaleY = image_yscale;\n"
SCALE_VARS_IN_STEP = True            # also put the two lines at the top of every Step event


def _scale_sync(obj):
    """scaleX = image_xscale; scaleY = image_yscale;  at the top of Create (and Step) of `obj`.
    Call it right after the object is created, before any other code is added."""
    gm.gm_add_event(obj, "create", SCALE_SYNC)
    if SCALE_VARS_IN_STEP:
        gm.gm_add_event(obj, "step", SCALE_SYNC)


def _sound_names(sound_files, symbols=None):
    """
    {sound_key: GameMaker sound name} - the FILE NAME, as it is:
        34_fire.mp3 -> 34_fire      rifle_asv.wav -> rifle_asv
    Characters GameMaker cannot use become "_"; a leading digit gets a "_" in front.
    """
    try:
        import as3_to_gml as _a2g
        reserved = _a2g.is_reserved
    except Exception:
        reserved = lambda n: False
    names, used = {}, set()
    for index, key in enumerate(sorted(sound_files), start=1):
        stem = os.path.splitext(os.path.basename(sound_files[key]))[0]
        name = re.sub(r"\W", "_", stem) or f"sound{index}"
        if name[0].isdigit():
            name = "_" + name
        if reserved(name):
            name = "snd_" + name
        names[key] = _unique_name(name, used)
    return names


def _class_sound_map(sound_files, symbols, sound_names):
    """{short AS3 class name: GM sound name} for every sound that has a class."""
    out = {}
    for sid, name in sound_names.items():
        cls = symbols.get(sid)
        if cls:
            out[_short_class(cls)] = name
    return out


def _fix_sound_refs(code, mapping):
    """audio_play_sound(snd_<Class>, ...)  ->  the real sound resource name."""
    for cls, name in (mapping or {}).items():
        code = re.sub(r"\bsnd_" + re.escape(cls) + r"\b", name, code)
    return code


def _placement_transform(placement, shapes):
    """SWF placement -> GameMaker x, y, rotation (counter-clockwise), xscale, yscale."""
    a, b, c, d, tx, ty = placement["m"]
    ox, oy = shapes.get(placement["charid"], (0.0, 0.0))
    x = tx + a * ox + c * oy          # exported images are cropped to the shape bounds
    y = ty + b * ox + d * oy
    scale_x = math.hypot(a, b)
    scale_y = math.hypot(c, d)
    if a * d - b * c < 0:             # mirrored
        scale_y = -scale_y
    rotation = -math.degrees(math.atan2(b, a))
    return x, y, rotation, scale_x, scale_y
 
 
def _select_frames(model, rooms_from):
    if rooms_from == "root":
        return model["main"]
    match = re.fullmatch(r"sprite:(\d+)", rooms_from)
    if not match:
        raise ValueError(f"Invalid rooms_from {rooms_from!r}; use 'root' or 'sprite:<id>'")
    sprite_id = int(match.group(1))
    if sprite_id not in model["sprites"]:
        raise ValueError(f"SWF has no DefineSprite with id {sprite_id}")
    return model["sprites"][sprite_id]
 
 
def _single_shape_plan(frames, model, shape_files):
    """
    A clip can be drawn by ONE GameMaker sprite when every frame shows exactly one shape, at the
    same place, unrotated and unmirrored, and all the shape images have the same size.
    Returns {"shapes": [shape id per frame], "x", "y", "sx", "sy"} or None.
    """
    if not frames:
        return None
    first, chosen = None, []
    for frame in frames:
        shown = frame["display"]
        if len(shown) != 1 or shown[0]["charid"] not in shape_files:
            return None
        t = _placement_transform(shown[0], model["shapes"])
        if first is None:
            first = t
        elif any(abs(a - b) > 0.5 for a, b in zip(t, first)):
            return None
        chosen.append(shown[0]["charid"])
    x, y, rot, sx, sy = first
    if abs(rot) > 0.01 or sx <= 0 or sy <= 0:
        return None
    try:
        sizes = {gm._png_size(shape_files[c]["png"]) for c in chosen}
    except (OSError, ValueError):
        return None
    if len(sizes) != 1:
        return None
    return {"shapes": chosen, "x": x, "y": y, "sx": sx, "sy": sy}


# A clip is baked into one sprite only when none of its child clips has an AS3 class of its own
# (those children must stay real objects so their code keeps running).  False = always bake.
ANIM_KEEP_CLASSED_CHILDREN = True


def export_animations(swf, xml_path, export_dir, java, ffdec_jar, fps=None, log=print):
    """Render every clip frame by frame with FFDec.  Returns {sprite_id: animation} (see swflib)."""
    log("Exporting animated sprites (one image per frame)...")
    rendered = swflib.export_sprite_frames(swf, export_dir, java, ffdec_jar)
    if not rendered:
        log("  FFDec wrote no sprite frames, animated clips keep the old behaviour. "
            + swflib._describe_dir(os.path.join(export_dir, "anim")))
        return {}
    anims, notes = swflib.read_sprite_animations(xml_path, rendered)
    for note in notes:
        log("  ! " + note)
    for anim in anims.values():
        anim["fps"] = fps
    log(f"  Animated sprites: {len(anims)}")
    return anims


def _link_animation(sprite_id, object_name, model, anim, class_of, used, linked, log):
    """Give a multi-frame clip ONE sprite with an image per frame.  True when it was linked."""
    a = (anim or {}).get(sprite_id)
    if not a:
        return False
    if ANIM_KEEP_CLASSED_CHILDREN:
        kids = {p["charid"] for fr in model["sprites"][sprite_id] for p in fr["display"]}
        if any(k in model["sprites"] and k in model["symbols"] for k in kids):
            log(f"  {object_name}: animated clip holds child clips with their own class, "
                f"children are spawned instead of baked into the sprite")
            return False
    base = object_name[4:] if object_name.startswith("obj_") else object_name
    sprite_name = _unique_name(gm.gm_sanitize_name("spr_" + base), used)
    try:
        gm.gm_create_sprite(sprite_name, frames=a["frames"], origin=tuple(a["origin"]),
                            fps=a.get("fps"))
    except (ValueError, OSError) as exc:
        log(f"  ! {object_name}: animation not used ({exc})")
        return False
    gm.gm_link_object_sprite(object_name, sprite_name)
    lines = [f"// Auto-generated from SWF sprite {sprite_id}: {a['count']}-frame animation drawn by "
             f"the sprite {sprite_name}, origin = the clip's origin.",
             "image_speed = 1;"]
    linked[sprite_id] = {"sprite": sprite_name, "create": "\n".join(lines) + "\n"}
    log(f"  animated {object_name} -> sprite {sprite_name} ({a['count']} frames"
        + (f", {a['fps']:g} fps" if a.get("fps") else "") + ")"
        + ("" if a.get("exact") else ", origin approximate"))
    return True


def link_sprites_to_objects(model, sprite_objects, shape_files, vector, class_objects, log=print, anim=None):
    """
    Link every SWF clip (and so its AS3 class) to a GameMaker sprite.

    A clip that is a single shape / a same-size animation of single shapes gets its own sprite
    (spr_<Class>), the origin set to the clip's origin, and is assigned to the clip's object.  Its
    Create code no longer spawns a separate child object.  Clips made of several parts keep the
    old behaviour (children spawned in Create) because one sprite cannot hold them.
    Returns {sprite_id: {"sprite": sprite name, "create": GML for the Create event}}.
    """
    class_of = {obj: cls for cls, obj in class_objects.items()}
    used = {n.lower() for n in gm.gm_list("sprites")}
    linked, multi = {}, []

    for sprite_id, object_name in sprite_objects.items():
        plan = _single_shape_plan(model["sprites"][sprite_id], model, shape_files)
        if plan is None:
            if _link_animation(sprite_id, object_name, model, anim, class_of, used, linked, log):
                continue
            if object_name in class_of:
                multi.append(class_of[object_name])
            continue
        shapes = plan["shapes"]
        base = object_name[4:] if object_name.startswith("obj_") else object_name
        sprite_name = _unique_name(gm.gm_sanitize_name("spr_" + base), used)
        svg = shape_files[shapes[0]].get("svg") if vector and len(shapes) == 1 else None
        if svg and not os.path.isfile(svg):
            svg = None
        # image top-left sits at (x, y) in clip space -> the clip origin is at image pixel (-x/sx, -y/sy)
        origin = (round(-plan["x"] / plan["sx"]), round(-plan["y"] / plan["sy"]))
        gm.gm_create_sprite(sprite_name, frames=[shape_files[c]["png"] for c in shapes],
                            origin=origin, svg=svg)
        gm.gm_link_object_sprite(object_name, sprite_name)

        lines = [f"// Auto-generated from SWF sprite {sprite_id}: drawn by the sprite {sprite_name} "
                 f"({len(shapes)} frame(s)), origin = the clip's origin."]
        if abs(plan["sx"] - 1) > 1e-4 or abs(plan["sy"] - 1) > 1e-4:
            lines.append(f"image_xscale = {plan['sx']:.5f}; image_yscale = {plan['sy']:.5f};")
        linked[sprite_id] = {"sprite": sprite_name, "create": "\n".join(lines) + "\n"}
        if object_name in class_of:
            log(f"  class {class_of[object_name]} -> {object_name} -> sprite {sprite_name}")

    log(f"  Sprites linked to objects: {len(linked)}/{len(sprite_objects)}")
    if multi:
        log("  Classes whose clip has several parts (children are spawned, no single sprite): "
            + ", ".join(sorted(multi)[:12]) + (" ..." if len(multi) > 12 else ""))
    return linked


def _sprite_object_code(sprite_id, frames, shapes, object_by_char):
    """GML Create code for a DefineSprite object: spawn its first-frame children."""
    lines = [f"// Auto-generated from SWF sprite {sprite_id} ({len(frames)} frame(s)).",
             "// Spawns the children of frame 1; positions are relative to this instance."]
    if frames:
        for placement in frames[0]["display"]:
            child = object_by_char.get(placement["charid"])
            if child is None:
                continue
            x, y, rot, sx, sy = _placement_transform(placement, shapes)
            lines.append(
                f"with (instance_create_depth(x + {x:.3f}, y + {y:.3f}, "
                f"depth - {placement['depth']}, {child})) {{ "
                f"image_xscale = {sx:.5f}; image_yscale = {sy:.5f}; "
                f"image_angle = {rot:.4f}; }}")
    return "\n".join(lines) + "\n"
 
 
# ---------------------------------------------------------------------------
# ActionScript 3 -> GML  (the integration)
# ---------------------------------------------------------------------------
 
def _has_code(gml):
    """False when the text is only comments / blank lines."""
    return any(l.strip() and not l.strip().startswith("//") for l in (gml or "").splitlines())
 
 
def _gm_event_key(event_name):
    """Translate standard and numbered GameMaker event names to gmlib keys."""
    if isinstance(event_name, tuple):
        return event_name
    name = str(event_name or "").strip()
    low = name.lower().replace(" ", "_")
    fixed = {
        "beginstep": "begin_step", "endstep": "end_step",
        "cleanup": "clean_up", "drawgui": "draw_gui",
        "drawbegin": "draw_begin", "drawend": "draw_end",
        "drawguibegin": "draw_gui_begin", "drawguiend": "draw_gui_end",
        "predraw": "pre_draw", "postdraw": "post_draw",
        "gamestart": "game_start", "gameend": "game_end",
        "roomstart": "room_start", "roomend": "room_end",
        "animationend": "animation_end",
    }
    low = fixed.get(low.replace("_", ""), low)
    if low in gm.EVENTS:
        return gm.EVENTS[low]

    numbered_types = {
        "alarm": 2, "step": 3, "keyboard": 5, "mouse": 6,
        "other": 7, "draw": 8, "keypress": 9, "keyrelease": 10,
    }
    match = re.fullmatch(
        r"(Alarm|Step|Keyboard|Mouse|Other|Draw|KeyPress|KeyRelease)_?(\d+)",
        name, re.IGNORECASE)
    if match:
        return (numbered_types[match.group(1).lower()], int(match.group(2)))

    if low.startswith("collision:"):
        other = name.split(":", 1)[1].strip()
        if other:
            return (4, other)
    if low.startswith("collision_"):
        other = name[len("Collision_"):].strip()
        if other:
            return (4, other)
    return gm._event_key(low)


def export_as3(swf, export_dir, java, ffdec_jar, log=print):
    """Let FFDec write every AS3 class as .as files; returns the folder holding them."""
    log("  Exporting ActionScript with FFDec...")
    swflib.ffdec(java, ffdec_jar, ["-export", "script", export_dir, os.path.abspath(swf)])
    scripts_dir = os.path.join(export_dir, "scripts")
    return scripts_dir if os.path.isdir(scripts_dir) else export_dir
 
 

def _patch_as3_events(events):
    """Patch all events of one AS3 class together for cross-event type inference."""
    import re
    events = dict(events)
    declaration_re = re.compile(
        r"\b(?:var\s+)?([A-Za-z_]\w*)\s*(?::\s*[A-Za-z_][\w.]*)?\s*=\s*"
        r"SharedObject\.getLocal\(\s*(['\"])(.*?)\2\s*\)\s*;?"
    )
    aliases = {}
    for code in events.values():
        for m in declaration_re.finditer(code or ""):
            aliases[m.group(1)] = m.group(3)

    if not aliases:
        return {name: _patch_hit_test(code or "") for name, code in events.items()}

    # Infer saved-field types across all events in this class.
    field_types = {}
    for alias in aliases:
        write_re = re.compile(r"\b" + re.escape(alias) + r"\.data\.([A-Za-z_]\w*)\s*=(?!=)\s*([^;]+);")
        for code in events.values():
            for m in write_re.finditer(code or ""):
                value = m.group(2).strip()
                field_types[(alias, m.group(1))] = "string" if re.match(r"^(['\"]).*\1$", value) else "real"

    output = {}
    for event_name, original in events.items():
        code = _patch_hit_test(original or "")
        used = [(a, f) for a, f in aliases.items()
                if re.search(r"\b" + re.escape(a) + r"\.data\.", code)
                or re.search(r"\b" + re.escape(a) + r"\.flush\s*\(", code)]
        for alias in aliases:
            code = declaration_re.sub(lambda m: "" if m.group(1) == alias else m.group(0), code)

        filenames = {f for _, f in used}
        # GameMaker can have only one INI file open at a time. Avoid corrupting
        # behavior if one event accesses multiple SharedObjects.
        if len(filenames) > 1:
            output[event_name] = code
            continue

        if used:
            filename = next(iter(filenames))
            if not re.search(r"\.[A-Za-z0-9]+$", filename):
                filename += ".ini"
            filename_gml = '"' + filename.replace('\\', '\\\\').replace('"', '\\"') + '"'

            for alias, _ in used:
                write_re = re.compile(r"\b" + re.escape(alias) + r"\.data\.([A-Za-z_]\w*)\s*=(?!=)\s*([^;]+);")
                def write_field(m):
                    key, value = m.group(1), m.group(2).strip()
                    fn = "ini_write_string" if field_types.get((alias, key)) == "string" else "ini_write_real"
                    return f'{fn}("data", "{key}", {value});'
                code = write_re.sub(write_field, code)

                # flush() commits the current writes, then reopens the file so
                # subsequent accesses in this event remain valid.
                flush_re = re.compile(r"\b" + re.escape(alias) + r"\.flush\s*\(\s*\)\s*;?")
                code = flush_re.sub(f"ini_close();\nini_open({filename_gml});", code)

                read_re = re.compile(r"\b" + re.escape(alias) + r"\.data\.([A-Za-z_]\w*)\b")
                def read_field(m):
                    key = m.group(1)
                    if field_types.get((alias, key)) == "string":
                        return f'ini_read_string("data", "{key}", "")'
                    return f'ini_read_real("data", "{key}", 0)'
                code = read_re.sub(read_field, code)

            code = f"ini_open({filename_gml});\n" + code.rstrip() + "\nini_close();\n"
        output[event_name] = code
    return output


def _patch_hit_test(code):
    """Test the receiver's bounding box against the requested object/instance."""
    import re
    expr = r"(?:\bself\b|\bother\b|[A-Za-z_]\w*)(?:\.[A-Za-z_]\w*)*"
    pattern = re.compile(r"(" + expr + r")\s*\.\s*hitTestObject\s*\(\s*(" + expr + r")\s*\)")
    def replace(m):
        a, b = m.group(1), m.group(2)
        return (f"collision_rectangle({a}.bbox_left, {a}.bbox_top, "
                f"{a}.bbox_right, {a}.bbox_bottom, {b}, false, true) != noone")
    return pattern.sub(replace, code)

def transpile_as2(as2_dir, object_names, log=print):
    """Convert exported AS2 sources into object-event or standalone-script results."""
    results = []
    if not os.path.isdir(as2_dir):
        raise NotADirectoryError(as2_dir)

    for folder, _, files in sorted(os.walk(as2_dir)):
        for fname in sorted(files):
            if not fname.lower().endswith(".as"):
                continue

            path = os.path.join(folder, fname)
            stem = os.path.splitext(fname)[0]
            try:
                with open(path, encoding="utf-8-sig", errors="replace") as fh:
                    source = fh.read()

                res = _a1g.as2_to_gml(
                    source,
                    name_hint=stem,
                    object_names=object_names
                )
                results.append({
                    "class": res.get("name") or stem,
                    "source": stem,
                    "events": res.get("events", []),
                    "kind": res.get("kind", "object"),
                    "compat": res.get("compatibility_objects", []),
                    "warnings": res.get("warnings", []),
                })

                for warning in res.get("warnings", []):
                    log(f"  ! {stem}: {warning}")

            except Exception as exc:
                log(f"  ! {stem}: AS2 conversion failed ({exc})")

    log(f"  AS2 files converted: {len(results)}")
    return results


def attach_as2(results, class_objects, doc_class, log=print):
    """Attach AS2 class events and standalone timeline scripts to the GM project.

    AS2 class results become Create/Step/Draw events. Timeline-script results
    become real GML script resources, invoked by a small persistent controller.
    """
    used = {n.lower() for n in gm.gm_list("objects")}
    doc_object = None
    script_calls = []
    script_ticks = []
    script_draws = []

    def ensure_controller():
        nonlocal doc_object
        if doc_object is not None:
            return doc_object

        doc_object = class_objects.get(doc_class)
        if doc_object is None:
            doc_object = _unique_name(
                gm.gm_sanitize_name("obj_" + (doc_class or "MainTimeline")),
                used
            )
            gm.gm_create_object(doc_object, persistent=True)
            _scale_sync(doc_object)
            class_objects[doc_class] = doc_object
        return doc_object

    for item in results:
        cls = item.get("class") or item.get("source") or "AS2Class"

        # AS2 converter may request compatibility objects (Sprite, TextField, etc.).
        compat = item.get("compat", [])
        if compat and hasattr(gm, "gm_apply_compatibility_objects"):
            for made in gm.gm_apply_compatibility_objects(
                    {"compatibility_objects": compat}):
                log(f"  compatibility object {made} created (used by {cls})")

        if item.get("kind") == "script":
            events = item.get("events", [])
            script_code = next(
                (ev.get("gml", "") for ev in events if ev.get("event") == "Script"),
                ""
            )
            if not _has_code(script_code):
                continue

            script_name = gm.gm_sanitize_name("scr_as2_" + cls)
            script_name = _unique_name(
                script_name, {n.lower() for n in gm.gm_list("scripts")}
            )
            gm.gm_create_script(script_name, script_code)

            # Calling the script resource makes its generated functions available.
            # RAW_TOP_LEVEL output also runs its top-level initialization here.
            script_calls.append(f"{script_name}();")
            if re.search(r"\\bfunction\\s+as2_timeline_start\\b", script_code):
                script_calls.append("as2_timeline_start();")
            if re.search(r"\\bfunction\\s+as2_timeline_tick\\b", script_code):
                script_ticks.append("as2_timeline_tick();")
            if re.search(r"\\bfunction\\s+as2_timeline_draw\\b", script_code):
                script_draws.append("as2_timeline_draw();")

            log(f"  {cls} -> {script_name}: standalone AS2 timeline script")
            continue

        events = item.get("events", [])
        if isinstance(events, dict):
            event_map = events
        else:
            event_map = {
                ev.get("event"): ev.get("gml", "")
                for ev in events if isinstance(ev, dict)
            }

        if not any(_has_code(event_map.get(k)) for k in ("Create", "Step", "Draw")) \
                and cls not in class_objects and cls != doc_class:
            continue

        obj = class_objects.get(cls)
        if obj is None:
            obj = _unique_name(gm.gm_sanitize_name("obj_" + cls), used)
            gm.gm_create_object(obj, persistent=(cls == doc_class))
            _scale_sync(obj)
            class_objects[cls] = obj

        written = []
        for event_name, gm_event in (
            ("Create", "create"), ("Step", "step"), ("Draw", "draw")
        ):
            code = event_map.get(event_name, "")
            if _has_code(code):
                gm.gm_add_event(obj, gm_event, code)
                written.append(event_name)

        if cls == doc_class:
            doc_object = obj
        log(f"  {cls} -> {obj}: {', '.join(written) or 'no code'}")

    if script_calls:
        controller = ensure_controller()
        gm.gm_add_event(controller, "create", "\\n".join(script_calls) + "\\n")
        if script_ticks:
            gm.gm_add_event(controller, "step", "\\n".join(script_ticks) + "\\n")
        if script_draws:
            gm.gm_add_event(controller, "draw", "\\n".join(script_draws) + "\\n")
        log(f"  AS2 timeline controller: {controller}")

    return doc_object


def transpile_as3(as3_dir, object_names, log=print):
    """
    Convert every .as file below as3_dir.
    Returns [{"class": "Player", "events": {"Create": gml, "Step": gml, "Draw": gml}}, ...]
    """
    import as3_to_gml as a2g
 
    results, failed = [], 0
    for folder, _, files in sorted(os.walk(as3_dir)):
        for fname in sorted(files):
            if not fname.lower().endswith(".as"):
                continue
            stem = os.path.splitext(fname)[0]
            try:
                with open(os.path.join(folder, fname), encoding="utf-8", errors="replace") as fh:
                    res = a2g.transpile(fh.read(), stem, object_names=object_names)
            except Exception as exc:        # one odd class must not stop the build
                failed += 1
                log(f"  ! {stem}: AS3 conversion failed ({exc})")
                continue
            for warning in res["warnings"]:
                log(f"  ! {res['name']}: {warning}")
            results.append({"class": res["name"],
                            "compat": res.get("compatibility_objects", []),
                            "events": _patch_as3_events({e["event"]: e["gml"] for e in res["events"]})})
    log(f"  AS3 classes converted: {len(results)}" + (f", {failed} failed" if failed else ""))
    return results
 
 
def create_compat_objects(log=print):
    """Put the AS3 stand-ins (obj_Sprite, obj_TextField) into the project and its .yyp."""
    try:
        import as3_to_gml as a2g
    except ImportError as exc:
        log(f"  Compatibility objects skipped: {exc}")
        return []
    specs = a2g.compat_specs(a2g.ALWAYS_COMPAT)
    made = gm.gm_apply_compatibility_objects({"compatibility_objects": specs})
    log("  Compatibility objects: " + ", ".join(s["name"] for s in specs)
        + (" (created)" if made else " (already present)"))
    return [s["name"] for s in specs]


def attach_as3(results, class_objects, doc_class, log=print, sound_names=None):
    """
    Write each class's Create / Step / Draw code into its GameMaker object.
    class_objects: {short class name: existing object name} for classes linked to a SWF sprite.
    Returns (document_object_name or None).
    """
    doc_object = None
    for item in results:                                # extra compat objects (MovieClip, Shape ...)
        for made in gm.gm_apply_compatibility_objects(
                {"compatibility_objects": item.get("compat", [])}):
            log(f"  compatibility object {made} created (used by {item['class']})")
    used = {n.lower() for n in gm.gm_list("objects")}
 
    for item in results:
        cls, events = item["class"], item["events"]
        if isinstance(events, dict):
            event_map = events
        else:
            event_map = {
                ev.get("event"): ev.get("gml", "")
                for ev in events if isinstance(ev, dict)
            }
        if not any(_has_code(code) for code in event_map.values()) \
                and cls not in class_objects and cls != doc_class:
            continue                                    # empty class / interface
 
        obj = class_objects.get(cls)
        if obj is None:                                 # class without a library clip
            obj = _unique_name(gm.gm_sanitize_name("obj_" + cls), used)
            gm.gm_create_object(obj, persistent=(cls == doc_class))
            _scale_sync(obj)
            class_objects[cls] = obj
        if cls == doc_class:
            doc_object = obj
 
        written = []
        for event_name, original_code in event_map.items():
            code = _fix_sound_refs(original_code or "", sound_names)
            if not _has_code(code):
                continue
            try:
                gm_event = _gm_event_key(event_name)
                # Create appends to any SWF child-spawn code already installed.
                gm.gm_add_event(obj, gm_event, code, append=True)
                written.append(str(event_name))
            except (ValueError, TypeError) as exc:
                log(f"  ! {cls}: unsupported GameMaker event {event_name!r} ({exc})")
        log(f"  {cls} -> {obj}: {', '.join(written) or 'no code'}")
    return doc_object
 
 
# ---------------------------------------------------------------------------
# Main conversion pipeline
# ---------------------------------------------------------------------------
 
def _resolve_out_dir(out_dir, swf):
    """
    Default / relative output folders are placed next to the SWF, so running the script from a
    protected folder (C:\\Windows\\System32) or an odd working directory still works.
    An absolute out_dir is used as given.  Raises a clear error if it cannot be written.
    """
    here = os.path.dirname(swf)
    if not out_dir:
        out_dir = os.path.join(here, "dist")
    elif not os.path.isabs(out_dir):
        cwd_target = os.path.abspath(out_dir)
        parent = cwd_target
        while not os.path.exists(parent):
            parent = os.path.dirname(parent)
        out_dir = cwd_target if os.access(parent, os.W_OK) else os.path.join(here, out_dir)
    out_dir = os.path.abspath(out_dir)
    try:
        os.makedirs(out_dir, exist_ok=True)
    except OSError as exc:
        raise RuntimeError(f"Cannot create the output folder {out_dir} ({exc}). "
                           f"Pass a writable folder, e.g. --out \"C:\\Users\\you\\Documents\\gm\"") from exc
    return out_dir
 
 
def run_pipeline(swf, name, java=DEFAULT_JAVA, ffdec_jar=DEFAULT_FFDEC, out_dir=None,
                 log=print, merge=None, vector=True, overwrite=False, template=None,
                 rooms_from="root", sounds=True, as3=True, as3_dir=None, main_class=None,
                 animate=True, as_version="as3"):
    """
    Convert an SWF into a GameMaker project and return the absolute .yyp path.
 
    merge:      {"src_label": "dst_label"} merges a room into another by room label.
    rooms_from: "root" or "sprite:<id>" (frames of one DefineSprite become rooms).
    out_dir:    parent folder of the project.  Default: a "dist" folder next to the SWF
                (not the current directory, which may be read-only, e.g. C:\\Windows\\System32).
    overwrite:  replace an existing <out_dir>/<name> project (default: refuse).
    template:   gmlib template folder (its options/ is copied); None = gmlib's default lookup.
    as3:        convert ActionScript into the objects' Create / Step / Draw events.
    as3_dir:    folder of .as files to use instead of exporting them with FFDec.
    main_class: document class name; default = the SWF's SymbolClass entry for the root.
    """
    if as_version not in ("as2", "as3", "none"):
        raise ValueError("as_version must be 'as2', 'as3', or 'none'")
    actionscript_enabled = bool(as3) and as_version != "none"

    swf = os.path.abspath(swf)
    if not os.path.isfile(swf):
        raise FileNotFoundError(f"SWF file not found: {swf}")
    out_dir = _resolve_out_dir(out_dir, swf)
 
    source_base = os.path.splitext(swf)[0]
    export_dir = source_base + "_export"
    xml_path = source_base + ".xml"
 
    project_root = os.path.join(out_dir, name)
    if os.path.exists(project_root) and not overwrite:
        raise FileExistsError(f"Project folder already exists: {project_root} "
                              f"(pass overwrite=True / --overwrite to replace it)")
 
    # ---- 1. extract -------------------------------------------------------
    log("Reading SWF header...")
    header = swflib.read_header(swf, java, ffdec_jar)
    width, height = header["width"] or 550, header["height"] or 400
    log(f"Resolution: {width}x{height}")
 
    log("Exporting SWF shapes...")
    shape_files = swflib.export_shapes(swf, export_dir, java, ffdec_jar, vector=vector)
 
    sound_files = {}
    if sounds:
        log("Exporting SWF sounds...")
        sound_files = swflib.export_sounds(swf, export_dir, java, ffdec_jar)
        log(f"  {len(sound_files)} sound file(s)")
 
    log("Converting SWF timeline to XML...")
    swflib.export_xml(swf, java, ffdec_jar, xml_path)
 
    log("Parsing SWF structure...")
    model = parse_swf(xml_path)
    log(f"  shapes={len(model['shapes'])} sprites={len(model['sprites'])} "
        f"symbols={len(model['symbols'])} main frames={len(model['main'])}")
 
    sound_names = _sound_names(sound_files, model["symbols"])
    anim = {}
    if animate:                          # clips with several frames -> one sprite, one image per frame
        anim = export_animations(swf, xml_path, export_dir, java, ffdec_jar,
                                 header.get("frame_rate"), log)

    as3_root = None
    if actionscript_enabled:
        try:
            as3_root = as3_dir or export_as3(swf, export_dir, java, ffdec_jar, log)
        except RuntimeError as exc:
            log(f"  ActionScript export skipped: {str(exc).splitlines()[0]}")
 
    # ---- 2. project, sprites, objects -------------------------------------
    log(f"Creating GameMaker project '{name}'...")
    gm.gm_create_project(name, out_dir=out_dir, overwrite=True, template=template)
    tpl = gm.gm_template_path(name)
    if tpl and os.path.isdir(os.path.join(project_root, "options")):
        log(f"  template options copied from: {tpl}")
    else:
        raise RuntimeError(
            "No template found. Objects are built from templateyyg/obj_template_svg/"
            "obj_template_svg.yy, so the unzipped 'templateyyg' folder is required: put it at "
            "<gmlib folder>/template/templateyyg or pass --template PATH.  "
            "(python gmlib.py shows where it looks)")
 
    object_by_char = {}                  # SWF character id -> GM object name
    used_objects = set()
    if actionscript_enabled and as_version == "as3":
        # AS3 compatibility stand-ins are only needed by the AVM2 frontend.
        used_objects.update(n.lower() for n in create_compat_objects(log))
 
    for index, (char_id, files) in enumerate(sorted(shape_files.items()), start=1):
        sprite_name = _resource_name("spr_shape", char_id)
        object_name = _resource_name("obj_shape", char_id)
        svg = files["svg"] if vector and files["svg"] and os.path.isfile(files["svg"]) else None
        gm.gm_create_sprite(sprite_name, frames=files["png"], origin="topleft", svg=svg)
        gm.gm_create_object(object_name, sprite=sprite_name)
        _scale_sync(object_name)
        object_by_char[char_id] = object_name
        used_objects.add(object_name.lower())
        if index % 25 == 0 or index == len(shape_files):
            log(f"  Shapes: {index}/{len(shape_files)}")
 
    # DefineSprite -> objects.  A clip with a linkage class gets obj_<Class>, which is
    # exactly the name `new Class()` is converted to, so AS3 and library line up.
    class_objects = {}                   # short class name -> object name
    sprite_objects = {}
    for sprite_id in model["sprites"]:
        linked = model["symbols"].get(sprite_id)
        if linked:
            object_name = _unique_name(gm.gm_sanitize_name("obj_" + _short_class(linked)),
                                       used_objects)
            class_objects[_short_class(linked)] = object_name
        else:
            object_name = _unique_name(_resource_name("obj_sprite", sprite_id), used_objects)
        gm.gm_create_object(object_name)
        object_by_char[sprite_id] = object_name
        sprite_objects[sprite_id] = object_name
 
    linked_sprites = link_sprites_to_objects(model, sprite_objects, shape_files, vector,
                                             class_objects, log, anim)
    for sprite_id, object_name in sprite_objects.items():
        code = _sprite_object_code(sprite_id, model["sprites"][sprite_id],
                                   model["shapes"], object_by_char)
        gm.gm_add_event(object_name, "create",
                        SCALE_SYNC + (linked_sprites.get(sprite_id, {}).get("create") or code))
    log(f"  Sprite objects: {len(sprite_objects)}")
    if SCALE_VARS_IN_STEP:
        for _o in sprite_objects.values():
            gm.gm_add_event(_o, "step", SCALE_SYNC)
 
    # ---- 3. ActionScript -> object events ---------------------------------
    doc_object = None
    if as3_root and actionscript_enabled:
        doc_class = main_class or (
            _short_class(model["symbols"][0])
            if 0 in model["symbols"] else "MainTimeline"
        )

        if as_version == "as2":
            log("Converting AS2 / AVM1 -> GML...")
            results = transpile_as2(as3_root, class_objects, log)
            doc_object = attach_as2(results, class_objects, doc_class, log)

        elif as_version == "as3":
            log("Converting AS3 / AVM2 -> GML...")
            results = transpile_as3(as3_root, class_objects, log)
            doc_object = attach_as3(
                results, class_objects, doc_class, log,
                sound_names=_class_sound_map(
                    sound_files, model["symbols"], sound_names
                )
            )

        if doc_object is None:
            log(f"  (no document class '{doc_class}' found among the converted classes)")
    # ---- 4. sounds --------------------------------------------------------
    sound_by_id = {}
    for sound_id, path in sorted(sound_files.items()):
        sound_name = sound_names.get(sound_id) or f"sound{sound_id}"
        try:
            gm.gm_create_sound(sound_name, path)
            sound_by_id[sound_id] = sound_name
        except Exception as exc:
            log(f"  Sound {sound_id} skipped: {exc}")
    if sound_by_id:
        log(f"  Sounds: {len(sound_by_id)}")
 
    # ---- 5. frames -> rooms ------------------------------------------------
    log("Building rooms...")
    frames = _select_frames(model, rooms_from)
 
    room_entries, order = {}, []
    for index, frame in enumerate(frames, start=1):
        label = frame["label"] or f"frame_{index}"
        entry = room_entries.setdefault(label, {"placements": [], "sounds": []})
        if label not in order:
            order.append(label)
        for placement in frame["display"]:
            object_name = object_by_char.get(placement["charid"])
            if object_name is None:
                continue
            x, y, rot, sx, sy = _placement_transform(placement, model["shapes"])
            entry["placements"].append({"object": object_name, "x": x, "y": y,
                                        "rotation": rot, "scale_x": sx, "scale_y": sy})
        entry["sounds"].extend(frame["sounds"])
 
    for source_label, target_label in (merge or {}).items():
        if source_label != target_label and source_label in room_entries \
                and target_label in room_entries:
            src = room_entries.pop(source_label)
            order.remove(source_label)
            room_entries[target_label]["placements"].extend(src["placements"])
            room_entries[target_label]["sounds"].extend(src["sounds"])
 
    made_rooms, used_rooms, first_room = 0, set(), None
    for label in order:
        entry = room_entries[label]
        if not entry["placements"]:
            continue
        room_name = _unique_name(_resource_name("room", label), used_rooms)
        gm.gm_create_room(room_name, width, height)
        gm.gm_add_instances(room_name, entry["placements"])
 
        play = [f"audio_play_sound({sound_by_id[s]}, 0, false);"
                for s in dict.fromkeys(entry["sounds"]) if s in sound_by_id]
        if play:
            gm.gm_set_room_code(room_name, "\n".join(play) + "\n")
 
        first_room = first_room or room_name
        made_rooms += 1
        log(f"  {room_name}: {len(entry['placements'])} instances"
            + (f", {len(play)} sound(s)" if play else ""))
 
    if made_rooms == 0:
        log("No timeline placements found; creating room_main with a shape grid.")
        room_name = _unique_name("room_main", used_rooms)
        gm.gm_create_room(room_name, width, height)
        columns = max(1, width // 100)
        shape_objects = [object_by_char[c] for c in sorted(model["shapes"]) if c in object_by_char]
        gm.gm_add_instances(room_name, [
            {"object": obj, "x": (i % columns) * 100, "y": (i // columns) * 100}
            for i, obj in enumerate(shape_objects)])
        first_room = room_name
        log(f"  {room_name}: {len(shape_objects)} instances")
 
    if doc_object and first_room:                       # the AS3 document class runs the game
        gm.gm_add_instance(first_room, doc_object, 0, 0)
        log(f"  Document class object {doc_object} placed in {first_room}")
 
    project_path = os.path.abspath(gm.gm_save_project())
    log("Checking the generated project...")
    check_project(project_path, log)
    log(f"Done: {project_path}")
    return project_path
 
 
# ---------------------------------------------------------------------------
# Project checker  (python avm2gml.py path\\to\\project.yyp)
# ---------------------------------------------------------------------------
 
def check_project(yyp_path, log=print):
    """
    Look for the things that make GameMaker say "Failed to add resource ... to storage":
    missing / unreadable .yy files, a .yy whose name does not match, names that differ only by
    case (same folder on Windows), objects whose event files are missing.
    Returns the list of problems (empty = looks fine).
    """
    import json
    root = os.path.dirname(os.path.abspath(yyp_path))
    problems = []
 
    def load(path):
        """GameMaker's .yy files allow trailing commas; strip them only to *read* the file."""
        with open(path, encoding="utf-8-sig") as fh:
            return json.loads(re.sub(r",(\s*[}\]])", r"\1", fh.read()))
 
    def bad(message):
        problems.append(message)
        log("  PROBLEM: " + message)
 
    try:
        project = load(yyp_path)
    except Exception as exc:
        bad(f"cannot read the .yyp: {exc}")
        return problems
 
    seen = {}
    for entry in project.get("resources", []):
        ref = entry.get("id", {})
        name, path = ref.get("name", "?"), ref.get("path", "")
        key = path.lower()
        if key in seen:
            bad(f"'{name}' and '{seen[key]}' differ only by letter case -> same folder on Windows ({path})")
            continue
        seen[key] = name
        full = os.path.join(root, *path.split("/"))
        if not os.path.isfile(full):
            bad(f"{path} is listed in the .yyp but the file does not exist")
            continue
        try:
            data = load(full)
        except Exception as exc:
            bad(f"{path} is not valid JSON ({exc})")
            continue
        if data.get("name") != name or os.path.basename(os.path.dirname(full)) != name:
            bad(f"{path}: name inside the file is {data.get('name')!r}, expected {name!r}")
        if path.startswith("objects/"):
            folder = os.path.dirname(full)
            for ev in data.get("eventList", []):
                etype, enum = ev.get("eventType"), ev.get("eventNum")
                if etype == 4:                     # collision: file is named after the other object
                    other = (ev.get("collisionObjectId") or {}).get("name", "")
                    fname = f"Collision_{other}.gml"
                else:
                    fname = f"{gm._EVENT_FILE.get(etype, 'Other')}_{enum}.gml"
                if not os.path.isfile(os.path.join(folder, fname)):
                    bad(f"{path}: event ({etype},{enum}) has no {fname}")
        if path.startswith("sprites/"):
            folder = os.path.dirname(full)
            for frame in data.get("frames", []):
                if not os.path.isfile(os.path.join(folder, frame.get("name", "?") + ".png")):
                    bad(f"{path}: frame {frame.get('name')} has no .png")
 
    for node in project.get("RoomOrderNodes", []):
        if node.get("roomId", {}).get("path", "").lower() not in seen:
            bad(f"room order lists a room that is not a resource: {node.get('roomId')}")
 
    options = os.path.join(root, "options")
    if not os.path.isdir(options):
        log("  note: no options/ folder (template not copied)")
    log(f"Checked {len(seen)} resources: " + (f"{len(problems)} problem(s)" if problems else "no problems found"))
    return problems
 
 
# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
 
def _parse_merge(values):
    result = {}
    for value in values:
        source, _, target = value.partition(":")
        if not source or not target:
            raise argparse.ArgumentTypeError(f"Invalid --merge value {value!r}; expected SRC:DST")
        result[source] = target
    return result or None
 
 
def main(argv=None):
    import sys
    args_in = sys.argv[1:] if argv is None else list(argv)
    if args_in and args_in[0].lower().endswith(".yyp"):       # python avm2gml.py my.yyp
        raise SystemExit(1 if check_project(args_in[0]) else 0)
 
    p = argparse.ArgumentParser(description="Convert SWF (+ AS3) to a GameMaker project")
    p.add_argument("swf", help="Input SWF file")
    p.add_argument("name", help="GameMaker project name")
    p.add_argument("--java", default=DEFAULT_JAVA, help="Path to java.exe")
    p.add_argument("--ffdec", default=DEFAULT_FFDEC, help="Path to ffdec-cli.jar")
    p.add_argument("--out", default=None,
                   help="Output parent directory (default: a 'dist' folder next to the SWF)")
    p.add_argument("--template", default=None, help="gmlib template folder (default: automatic)")
    p.add_argument("--overwrite", action="store_true", help="Replace an existing project folder")
    p.add_argument("--rooms-from", default="root", metavar="root|sprite:ID",
                   help="Timeline whose frames become rooms (default: root)")
    p.add_argument("--merge", action="append", default=[], metavar="SRC:DST",
                   help="Merge one room label into another; can be repeated")
    p.add_argument("--no-vector", action="store_true", help="PNG sprites only; no SVG")
    p.add_argument("--no-sounds", action="store_true", help="Do not export/import sounds")
    p.add_argument("--no-as3", action="store_true", help="Skip the ActionScript -> GML conversion")
    p.add_argument("--no-anim", action="store_true",
                   help="Do not render multi-frame clips as animated sprites")
    p.add_argument("--as3-dir", default=None, help="Use the .as files in this folder instead of "
                                                   "exporting them with FFDec")
    p.add_argument("--main", default=None, metavar="CLASS",
                   help="Document class name (default: taken from the SWF)")
    p.add_argument("--as-version", choices=("as2", "as3", "none"), default="as3",
                   help="ActionScript version to convert (default: as3)")
    a = p.parse_args(args_in)
 
    run_pipeline(a.swf, a.name, java=a.java, ffdec_jar=a.ffdec, out_dir=a.out,
                 merge=_parse_merge(a.merge), vector=not a.no_vector, overwrite=a.overwrite,
                 template=a.template, rooms_from=a.rooms_from, sounds=not a.no_sounds,
                 as3=not a.no_as3, as3_dir=a.as3_dir, main_class=a.main,
                 animate=not a.no_anim, as_version=a.as_version)
 
 
if __name__ == "__main__":
    main()
 