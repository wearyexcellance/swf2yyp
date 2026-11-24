"""
gmlib.py - build GameMaker (2.3+ / 2024 project format) projects from Python.
 
Project files are generated here. A GameMaker object template is required for .yy objects.
 
Typical use:
 
    from gmlib import *
 
    gm_create_project("cha")                       # -> "cha"
    gm_create_sprite("spr_hero", ["hero.png"])     # -> "spr_hero"
    gm_create_object("obj_hero", sprite="spr_hero")
    gm_add_event("obj_hero", "step", "x += 1;")
    gm_create_room("room_main", 1366, 768)         # -> "room_main"
    gm_add_instance("room_main", "obj_hero", 100, 100)
    gm_create_sound("snd_jump", "jump.wav")
 
Every function takes an optional `project=` argument. If you leave it out,
the most recently created project is used.
"""
 
import json
import os
import re
import shutil
import struct
import sys
import uuid
import wave
import zlib
 
# Written into the .yyp. Change it if your IDE complains about the version.
IDE_VERSION = "2024.14.4.222"  # matches template
 
_NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
_projects = {}
_current = None
 
# Static files (the options/ folder) are copied from the template project, i.e. the
# unzipped 'templateyyg' folder, looked up at ./template/templateyyg or next to this file.
_HERE = os.path.dirname(os.path.abspath(__file__))
TEMPLATE_CANDIDATES = [os.path.join("template", "templateyyg"),
                       os.path.join(_HERE, "template", "templateyyg")]
 
# Every new object starts with these four events, in this order, like the template.
PLACEHOLDER_EVENTS = {
    (0, 0): "//Create script here",
    (3, 1): "//BEGIN STEP script here",
    (3, 0): "//NORMAL STEP script here",
    (8, 0): "draw_self()",
}
 
ORIGINS = {
    "topleft": 0, "topcenter": 1, "topright": 2,
    "middleleft": 3, "center": 4, "middleright": 5,
    "bottomleft": 6, "bottomcenter": 7, "bottomright": 8,
}
 
# event name -> (eventType, eventNum)
EVENTS = {
    "create": (0, 0), "destroy": (1, 0), "clean_up": (12, 0),
    "begin_step": (3, 1), "step": (3, 0), "end_step": (3, 2),
    "draw": (8, 0), "draw_gui": (8, 64),
    "draw_begin": (8, 72), "draw_end": (8, 73),
    "draw_gui_begin": (8, 74), "draw_gui_end": (8, 75),
    "pre_draw": (8, 76), "post_draw": (8, 77),
    "game_start": (7, 2), "game_end": (7, 3),
    "room_start": (7, 4), "room_end": (7, 5), "animation_end": (7, 7),
}
_EVENT_FILE = {0: "Create", 1: "Destroy", 2: "Alarm", 3: "Step", 4: "Collision",
               5: "Keyboard", 6: "Mouse", 7: "Other", 8: "Draw",
               9: "KeyPress", 10: "KeyRelease", 12: "CleanUp"}
 
 
# ----------------------------------------------------------------------
# internals
# ----------------------------------------------------------------------
class _Project:
    def __init__(self, name, root):
        self.name = name
        self.root = root
        self.sprites = {}
        self.objects = {}
        self.rooms = {}
        self.sounds = {}
        self.scripts = {}
        self.room_order = []
        self.template = None
        self.obj_template = None      # text of templateyyg/obj_template_svg/obj_template_svg.yy
 
 
def _uid():
    return str(uuid.uuid4())
 
 
def _check_name(name):
    if not isinstance(name, str) or not _NAME_RE.match(name):
        raise ValueError(f"Invalid GameMaker resource name: {name!r} "
                         "(letters, digits, underscore; cannot start with a digit)")
    return name
 
 
def _proj(project=None):
    key = project or _current
    if key is None:
        raise RuntimeError("No project yet. Call gm_create_project(name) first.")
    if key not in _projects:
        raise KeyError(f"Unknown project: {key!r}")
    return _projects[key]
 
 
def _ref(kind, name):
    return {"name": name, "path": f"{kind}/{name}/{name}.yy"}
 
 
def _parent(p):
    # The template puts every resource directly under the project, no folders.
    return {"name": p.name, "path": f"{p.name}.yyp"}
 
 

 
def _write_json(path, data):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
 
 
def _write_text(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)
 
 
def _reset_dir(path):
    if os.path.isdir(path):
        shutil.rmtree(path)
    os.makedirs(path)
 
 
def _png_size(path):
    with open(path, "rb") as f:
        head = f.read(24)
    if head[:8] != b"\x89PNG\r\n\x1a\n":
        raise ValueError(f"Not a PNG file: {path}")
    return struct.unpack(">II", head[16:24])
 
 
def _blank_png(w, h):
    def chunk(tag, data):
        c = struct.pack(">I", len(data)) + tag + data
        return c + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF)
 
    raw = (b"\x00" + b"\x00" * (4 * w)) * h
    return (b"\x89PNG\r\n\x1a\n"
            + chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 6, 0, 0, 0))
            + chunk(b"IDAT", zlib.compress(raw))
            + chunk(b"IEND", b""))
 
 
# ----------------------------------------------------------------------
# writers (one per resource kind)
# ----------------------------------------------------------------------
def _write_yyp(p):
    resources = []
    for kind, table in (("sprites", p.sprites), ("objects", p.objects),
                        ("sounds", p.sounds), ("scripts", p.scripts),
                        ("rooms", p.rooms)):
        resources += [{"id": _ref(kind, n)} for n in table]
 
    data = {
        "$GMProject": "v1",
        "%Name": p.name,
        "AudioGroups": [{"$GMAudioGroup": "v1", "%Name": "audiogroup_default",
                         "exportDir": "", "name": "audiogroup_default",
                         "resourceType": "GMAudioGroup", "resourceVersion": "2.0",
                         "targets": -1}],
        "configs": {"children": [], "name": "Default"},
        "defaultScriptType": 0,
        "Folders": [],
        "ForcedPrefabProjectReferences": [],
        "IncludedFiles": [],
        "isEcma": False,
        "LibraryEmitters": [],
        "MetaData": {"IDEVersion": IDE_VERSION},
        "name": p.name,
        "resources": resources,
        "resourceType": "GMProject",
        "resourceVersion": "2.0",
        "RoomOrderNodes": [{"roomId": _ref("rooms", n)} for n in p.room_order],
        "templateType": "game",
        "TextureGroups": [{"$GMTextureGroup": "", "%Name": "Default", "autocrop": True,
                           "border": 2, "compressFormat": "bz2", "customOptions": "",
                           "directory": "", "groupParent": None, "isScaled": True,
                           "loadType": "default", "mipsToGenerate": 0, "name": "Default",
                           "resourceType": "GMTextureGroup", "resourceVersion": "2.0",
                           "targets": -1}],
    }
    _write_json(os.path.join(p.root, f"{p.name}.yyp"), data)
 
    ordered = [{"name": r["id"]["name"], "order": i, "path": r["id"]["path"]}
               for i, r in enumerate(resources, 1)]
    _write_json(os.path.join(p.root, f"{p.name}.resource_order"),
                {"FolderOrderSettings": [], "ResourceOrderSettings": ordered})
 
 
def _write_sprite(p, name):
    s = p.sprites[name]
    w, h = s["w"], s["h"]
    d = os.path.join(p.root, "sprites", name)
    _reset_dir(d)
 
    layer_id = _uid()
    frame_ids = [_uid() for _ in range(max(1, len(s["frames"])))]
 
    for i, fid in enumerate(frame_ids):
        if s.get("svg"):
            # vector sprite, like the template: <frame>.svg + <frame>.png, no layers folder
            shutil.copyfile(s["svg"][min(i, len(s["svg"]) - 1)], os.path.join(d, f"{fid}.svg"))
            targets = [os.path.join(d, f"{fid}.png")]
        else:
            targets = [os.path.join(d, f"{fid}.png"),
                       os.path.join(d, "layers", fid, f"{layer_id}.png")]
        for target in targets:
            os.makedirs(os.path.dirname(target), exist_ok=True)
            if s["frames"]:
                shutil.copyfile(s["frames"][i], target)
            else:
                with open(target, "wb") as f:
                    f.write(_blank_png(w, h))
 
    origin = s["origin"]
    if isinstance(origin, tuple):
        origin_id, ox, oy = 9, origin[0], origin[1]
    else:
        origin_id = ORIGINS[origin]
        ox = w / 2 * (origin_id % 3)
        oy = h / 2 * (origin_id // 3)
 
    n = len(frame_ids)
    keyframes = [{
        "$Keyframe<SpriteFrameKeyframe>": "",
        "Channels": {"0": {"$SpriteFrameKeyframe": "",
                           "Id": {"name": fid, "path": f"sprites/{name}/{name}.yy"},
                           "resourceType": "SpriteFrameKeyframe", "resourceVersion": "2.0"}},
        "Disabled": False, "id": _uid(), "IsCreationKey": False,
        "Key": float(i), "Length": 1.0,
        "resourceType": "Keyframe<SpriteFrameKeyframe>", "resourceVersion": "2.0",
        "Stretch": False,
    } for i, fid in enumerate(frame_ids)]
 
    data = {
        "$GMSprite": "v2",
        "%Name": name,
        "bboxMode": 0,
        "bbox_bottom": h - 1, "bbox_left": 0, "bbox_right": w - 1, "bbox_top": 0,
        "collisionKind": 1,
        "collisionTolerance": 0,
        "DynamicTexturePage": False,
        "edgeFiltering": False,
        "For3D": False,
        "frames": [{"$GMSpriteFrame": "v1", "%Name": fid, "name": fid,
                    "resourceType": "GMSpriteFrame", "resourceVersion": "2.0"}
                   for fid in frame_ids],
        "gridX": 0, "gridY": 0,
        "height": h,
        "HTile": False,
        "layers": [{"$GMImageLayer": "", "%Name": layer_id, "blendMode": 0,
                    "displayName": "default", "isLocked": False, "name": layer_id,
                    "opacity": 100.0, "resourceType": "GMImageLayer",
                    "resourceVersion": "2.0", "visible": True}],
        "name": name,
        "nineSlice": None,
        "origin": origin_id,
        "parent": _parent(p),
        "preMultiplyAlpha": False,
        "resourceType": "GMSprite",
        "resourceVersion": "2.0",
        "sequence": {
            "$GMSequence": "v1", "%Name": name, "autoRecord": True,
            "backdropHeight": 768, "backdropImageOpacity": 0.5, "backdropImagePath": "",
            "backdropWidth": 1366, "backdropXOffset": 0.0, "backdropYOffset": 0.0,
            "events": {"$KeyframeStore<MessageEventKeyframe>": "", "Keyframes": [],
                       "resourceType": "KeyframeStore<MessageEventKeyframe>",
                       "resourceVersion": "2.0"},
            "eventStubScript": None, "eventToFunction": {},
            "length": float(n), "lockOrigin": False,
            "moments": {"$KeyframeStore<MomentsEventKeyframe>": "", "Keyframes": [],
                        "resourceType": "KeyframeStore<MomentsEventKeyframe>",
                        "resourceVersion": "2.0"},
            "name": name, "playback": 1, "playbackSpeed": float(s.get("fps") or 30.0),
            "playbackSpeedType": 0,
            "resourceType": "GMSequence", "resourceVersion": "2.0",
            **({} if s.get("svg") else {"seqHeight": float(h), "seqWidth": float(w)}),
            "showBackdrop": True, "showBackdropImage": False, "timeUnits": 1,
            "tracks": [{
                "$GMSpriteFramesTrack": "", "builtinName": 0, "events": [],
                "inheritsTrackColour": True, "interpolation": 1, "isCreationTrack": False,
                "keyframes": {"$KeyframeStore<SpriteFrameKeyframe>": "",
                              "Keyframes": keyframes,
                              "resourceType": "KeyframeStore<SpriteFrameKeyframe>",
                              "resourceVersion": "2.0"},
                "modifiers": [], "name": "frames",
                "resourceType": "GMSpriteFramesTrack", "resourceVersion": "2.0",
                "spriteId": None, "trackColour": 0, "tracks": [], "traits": 0,
            }],
            "visibleRange": None, "volume": 1.0,
            "xorigin": int(ox), "yorigin": int(oy),
        },
        "swatchColours": None,
        "swfPrecision": 0.5 if s.get("svg") else 2.525,
        "textureGroupId": {"name": "Default", "path": "texturegroups/Default"},
        "type": 3 if s.get("svg") else 0,
        "VTile": False,
        "width": w,
    }
    _write_json(os.path.join(d, f"{name}.yy"), data)
 
 
def _event_key(ev):
    if isinstance(ev, tuple):
        return ev
    e = str(ev).lower().strip()
    m = re.fullmatch(r"alarm_?(\d+)", e)
    if m:
        return (2, int(m.group(1)))
    if e.startswith("collision:"):
        return (4, e.split(":", 1)[1].strip())
    if e in EVENTS:
        return EVENTS[e]
    raise ValueError(f"Unknown event {ev!r}. Known: {sorted(EVENTS)}, alarmN, "
                     "collision:obj_name, or a raw (type, num) tuple.")
 
 
OBJECT_TEMPLATE = "obj_template_svg"
 
 
def _object_template(p):
    """
    Text of the template object  <template>/obj_template_svg/obj_template_svg.yy.
    Object files are made by copying this file and substituting values with regex:
    GameMaker's .yy files are not strict JSON (trailing commas, exact layout), so they
    are never parsed and re-written.
    """
    if p.obj_template is not None:
        return p.obj_template
    tpl = p.template
    if not tpl:
        raise FileNotFoundError(
            "No template folder, so no object template. Put the unzipped 'templateyyg' folder "
            f"(with {OBJECT_TEMPLATE}/{OBJECT_TEMPLATE}.yy and options/) next to gmlib.py "
            "under template/templateyyg, or pass template=PATH to gm_create_project().")
    fname = OBJECT_TEMPLATE + ".yy"
    candidates = [os.path.join(tpl, OBJECT_TEMPLATE, fname),
                  os.path.join(tpl, "objects", OBJECT_TEMPLATE, fname)]
    for folder, _, files in os.walk(tpl):
        if fname in files:
            candidates.append(os.path.join(folder, fname))
    for path in candidates:
        if os.path.isfile(path):
            with open(path, encoding="utf-8-sig") as f:
                p.obj_template = f.read()
            return p.obj_template
    raise FileNotFoundError(f"Template object not found: expected {candidates[0]}")
 
 
def _sub1(pattern, repl_value, text, flags=0):
    """re.sub once, keeping group 1 (the '"key":' part) and replacing the value."""
    return re.sub(pattern, lambda m: m.group(1) + repl_value, text, count=1, flags=flags)
 
 
def _render_object(template, p, name, o, events):
    """
    Build an object .yy from the template text with regex substitutions only.
    events: [(eventType, eventNum, collision_object_name_or_None), ...]
    """
    t = template.replace(OBJECT_TEMPLATE, name)            # "%Name" and "name"
 
    # parent -> this project (the template keeps every resource directly under the project)
    t = re.sub(r'("parent"\s*:\s*\{\s*"name"\s*:\s*)"[^"]*"(\s*,\s*"path"\s*:\s*)"[^"]*"',
               lambda m: f'{m.group(1)}{json.dumps(p.name)}{m.group(2)}{json.dumps(p.name + ".yyp")}',
               t, count=1)
 
    def ref(kind, n):
        return '{"name":%s,"path":%s,}' % (json.dumps(n), json.dumps(f"{kind}/{n}/{n}.yy"))
 
    t = _sub1(r'("spriteId"\s*:\s*)(?:null|\{[^{}]*\})',
              ref("sprites", o["sprite"]) if o["sprite"] else "null", t)
    t = _sub1(r'("parentObjectId"\s*:\s*)(?:null|\{[^{}]*\})',
              ref("objects", o["parent"]) if o["parent"] else "null", t)
    for key in ("persistent", "visible", "solid"):
        t = _sub1(rf'("{key}"\s*:\s*)(?:true|false)', "true" if o[key] else "false", t)
 
    # event list: every event item is the template's first item with new numbers
    m = re.search(r'("eventList"\s*:\s*\[)(.*?)(\]\s*,)', t, re.S)
    if not m:
        raise ValueError("template object has no eventList")
    body = m.group(2)
    found = re.findall(r'\{[^{}]*\}', body)
    if not found:
        raise ValueError("template object has an empty eventList; keep at least one event in "
                         f"{OBJECT_TEMPLATE}.yy so its format can be copied")
    pattern = found[0]
    items = []
    for etype, enum, other in events:
        item = _sub1(r'("eventType"\s*:\s*)-?\d+', str(etype), pattern)
        item = _sub1(r'("eventNum"\s*:\s*)-?\d+', str(enum), item)
        item = _sub1(r'("collisionObjectId"\s*:\s*)(?:null|\{[^{}]*\})',
                     ref("objects", other) if other else "null", item)
        items.append(item)
    lead = re.match(r'\s*', body).group(0)
    tail = re.search(r'\s*$', body).group(0)
    sep = "," + lead
    new_body = (lead + sep.join(items) + ("," if items else "")) if items else ""
    new_body += tail if items else ""
    t = t[:m.start(2)] + new_body + t[m.end(2):]
    return t
 
 
def _write_object(p, name):
    o = p.objects[name]
    template = _object_template(p)             # fail early with a clear message
    d = os.path.join(p.root, "objects", name)
    _reset_dir(d)
 
    events = []
    for (etype, enum), code in o["events"].items():
        if etype == 4:  # collision: enum holds the other object's name
            fname = f"Collision_{enum}.gml"
            events.append((4, 0, enum))
        else:
            fname = f"{_EVENT_FILE.get(etype, 'Other')}_{enum}.gml"
            events.append((etype, enum, None))
        _write_text(os.path.join(d, fname), code)
    _write_text(os.path.join(d, f"{name}.yy"), _render_object(template, p, name, o, events))
 
 
def _write_room(p, name):
    r = p.rooms[name]
    d = os.path.join(p.root, "rooms", name)
    _reset_dir(d)
 
    instances, order = [], []
    for inst in r["instances"]:
        iname = inst["name"]
        order.append({"name": iname, "path": f"rooms/{name}/{name}.yy"})
        instances.append({
            "$GMRInstance": "v1", "%Name": iname, "colour": 4294967295, "frozen": False,
            "hasCreationCode": False, "ignore": False, "imageIndex": 0, "imageSpeed": 1.0,
            "inheritCode": False, "inheritedItemId": None, "inheritItemSettings": False,
            "isDnd": False, "name": iname, "objectId": _ref("objects", inst["object"]),
            "properties": [], "resourceType": "GMRInstance", "resourceVersion": "2.0",
            "rotation": float(inst["rotation"]),
            "scaleX": float(inst["scale_x"]), "scaleY": float(inst["scale_y"]),
            "x": float(inst["x"]), "y": float(inst["y"]),
        })
 
    code_file = ""
    if r["code"].strip():
        _write_text(os.path.join(d, "RoomCreationCode.gml"), r["code"])
        code_file = f"${{project_dir}}/rooms/{name}/RoomCreationCode.gml"
 
    w, h = r["w"], r["h"]
    view = {"hborder": 32, "hport": h, "hspeed": -1, "hview": h, "inherit": False,
            "objectId": None, "vborder": 32, "visible": False, "vspeed": -1,
            "wport": w, "wview": w, "xport": 0, "xview": 0, "yport": 0, "yview": 0}
 
    data = {
        "$GMRoom": "v1",
        "%Name": name,
        "creationCodeFile": code_file,
        "inheritCode": False, "inheritCreationOrder": False, "inheritLayers": False,
        "instanceCreationOrder": order,
        "isDnd": False,
        "layers": [{
            "$GMRInstanceLayer": "", "%Name": "Instances", "depth": 0,
            "effectEnabled": True, "effectType": None, "gridX": 32, "gridY": 32,
            "hierarchyFrozen": False, "inheritLayerDepth": False,
            "inheritLayerSettings": False, "inheritSubLayers": True,
            "inheritVisibility": True, "instances": instances, "layers": [],
            "name": "Instances", "properties": [],
            "resourceType": "GMRInstanceLayer", "resourceVersion": "2.0",
            "userdefinedDepth": False, "visible": True,
        }, {
            "$GMRBackgroundLayer": "", "%Name": "Background", "animationFPS": 15.0,
            "animationSpeedType": 0, "colour": 4278190080, "depth": 100,
            "effectEnabled": True, "effectType": None, "gridX": 32, "gridY": 32,
            "hierarchyFrozen": False, "hspeed": 0.0, "htiled": False,
            "inheritLayerDepth": False, "inheritLayerSettings": False,
            "inheritSubLayers": True, "inheritVisibility": True, "layers": [],
            "name": "Background", "properties": [],
            "resourceType": "GMRBackgroundLayer", "resourceVersion": "2.0",
            "spriteId": None, "stretch": False, "userdefinedAnimFPS": False,
            "userdefinedDepth": False, "visible": True, "vspeed": 0.0, "vtiled": False,
            "x": 0, "y": 0,
        }],
        "name": name,
        "parent": _parent(p),
        "parentRoom": None,
        "physicsSettings": {"inheritPhysicsSettings": False, "PhysicsWorld": False,
                            "PhysicsWorldGravityX": 0.0, "PhysicsWorldGravityY": 10.0,
                            "PhysicsWorldPixToMetres": 0.1},
        "resourceType": "GMRoom",
        "resourceVersion": "2.0",
        "roomSettings": {"Height": h, "inheritRoomSettings": False,
                         "persistent": False, "Width": w},
        "sequenceId": None,
        "views": [dict(view) for _ in range(8)],
        "viewSettings": {"clearDisplayBuffer": True, "clearViewBackground": False,
                         "enableViews": False, "inheritViewSettings": False},
        "volume": 1.0,
    }
    _write_json(os.path.join(d, f"{name}.yy"), data)
 
 
def _write_sound(p, name):
    s = p.sounds[name]
    d = os.path.join(p.root, "sounds", name)
    _reset_dir(d)

    fname = name + s["ext"]
    if s["src"]:
        shutil.copyfile(s["src"], os.path.join(d, fname))
    else:
        _silent_wav(os.path.join(d, fname))

    duration, rate, depth = 0.0, 44100, 1

    if s["ext"] == ".wav":
        with wave.open(os.path.join(d, fname), "rb") as w:
            rate = w.getframerate()
            duration = w.getnframes() / float(rate)
            depth = 1 if w.getsampwidth() >= 2 else 0

    data = {
        "$GMSound": "v2",
        "%Name": name,

        "audioGroupId": {
            "name": "audiogroup_default",
            "path": "audiogroups/audiogroup_default",
        },

        "bitDepth": depth,
        "channelFormat": 0,
        "compression": 0,
        "compressionQuality": 4,
        "conversionMode": 0,
        "duration": duration,
        "exportDir": "",
        "name": name,

        "parent": _parent(p),

        "preload": False,
        "resourceType": "GMSound",
        "resourceVersion": "2.0",
        "sampleRate": rate,
        "soundFile": fname,
        "volume": float(s["volume"]),
    }

    _write_json(os.path.join(d, f"{name}.yy"), data)
 
def _silent_wav(path, seconds=0.1, rate=44100):
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(b"\x00\x00" * int(rate * seconds))
 
 
def _write_script(p, name):
    d = os.path.join(p.root, "scripts", name)
    _reset_dir(d)
    _write_text(os.path.join(d, f"{name}.gml"), p.scripts[name]["code"])
    _write_json(os.path.join(d, f"{name}.yy"), {
        "$GMScript": "v1", "%Name": name, "isCompatibility": False, "isDnD": False,
        "name": name, "parent": _parent(p),
        "resourceType": "GMScript", "resourceVersion": "2.0",
    })
 
 
# ----------------------------------------------------------------------
# PUBLIC API
# ----------------------------------------------------------------------
def gm_sanitize_name(text, prefix="r_"):
    """Turn any string into a legal GameMaker resource name."""
    s = re.sub(r"[^A-Za-z0-9_]", "_", str(text))
    return s if s and not s[0].isdigit() else prefix + s
 
 
def _template_candidates():
    """Folders that may be the template (the one that directly contains options/)."""
    out = []
    for root in (os.getcwd(), _HERE):
        out += [os.path.join(root, "template", "templateyyg"),
                os.path.join(root, "template"),
                os.path.join(root, "templateyyg")]
    return list(dict.fromkeys(out))
 
 
def _is_template(path):
    return bool(path) and os.path.isdir(os.path.join(path, "options"))
 
 
def _find_template(template, searched=None):
    """
    Return the folder whose options/ gets copied, or None.
    Checks the explicit `template` (or the usual places), then looks up to 3 levels
    deeper - unzipping often gives template/templateyyg/templateyyg/options.
    `searched` (a list) receives every folder that was looked at.
    """
    bases = [template] if template else _template_candidates()
    searched = searched if searched is not None else []
    for base in bases:
        searched.append(base)
        if _is_template(base):
            return base
    for base in bases:
        if not base or not os.path.isdir(base):
            continue
        base_depth = base.rstrip("\\/").count(os.sep)
        for folder, dirs, _ in os.walk(base):
            if folder.rstrip("\\/").count(os.sep) - base_depth >= 3:
                dirs[:] = []
                continue
            dirs[:] = [d for d in dirs if d != "options"]
            if _is_template(folder):
                searched.append(folder)
                return folder
    return None
 
 
def gm_create_project(name, out_dir="dist", overwrite=True, template=None):
    """
    Create an empty project on disk. Returns the project name.
    template: folder of the unzipped 'templateyyg'. Its options/ folder is copied
    into the new project. Default: ./template/templateyyg if it exists.
    """
    global _current
    _check_name(name)
    root = os.path.join(out_dir, name)
    if os.path.exists(root):
        if not overwrite:
            raise FileExistsError(root)
        shutil.rmtree(root)
    os.makedirs(root)
    searched = []
    tpl = _find_template(template, searched)
    if template and not tpl:
        raise FileNotFoundError(f"Template has no options/ folder: {template}")
    if not tpl:
        print("gmlib WARNING: template not found - the project will have NO options/ folder.\n"
              "  Put the unzipped 'templateyyg' folder (the one containing options/) at\n"
              f"    {os.path.join(_HERE, 'template', 'templateyyg')}\n"
              "  or pass template=PATH. Looked in:\n    " + "\n    ".join(searched),
              file=sys.stderr)
    if tpl:
        shutil.copytree(os.path.join(tpl, "options"), os.path.join(root, "options"))
    _projects[name] = _Project(name, root)
    _projects[name].template = tpl
    _current = name
    _write_yyp(_projects[name])
    return name
 
 
def gm_use_project(name):
    """Switch which project functions act on when `project=` is omitted."""
    global _current
    _proj(name)
    _current = name
    return name
 
 
def gm_template_path(project=None):
    """Folder the project's options/ was copied from (None = nothing was copied)."""
    return _proj(project).template
 
 
def gm_project_path(project=None):
    """Path to the .yyp file."""
    p = _proj(project)
    return os.path.join(p.root, f"{p.name}.yyp")
 
 
def gm_save_project(project=None):
    """Re-write the .yyp. Every gm_create_* already does this; call it if in doubt."""
    p = _proj(project)
    _write_yyp(p)
    return gm_project_path(project)
 
 
def gm_list(kind, project=None):
    """List resource names. kind: sprites | objects | rooms | sounds | scripts."""
    return list(getattr(_proj(project), kind))
 
 
# ---- sprites ---------------------------------------------------------
def gm_create_sprite(name, frames=None, width=32, height=32, origin="center",
                     svg=None, fps=None, project=None):
    """
    frames: a PNG path, or a list of PNG paths (animation). None -> blank sprite.
    origin: 'center', 'topleft', 'bottomcenter', ... or an (x, y) tuple.
    svg: optional .svg file, or a list with one .svg per frame. Makes a vector sprite exactly like
         the template (<frame>.svg + <frame>.png). `frames` should then hold the matching PNGs.
         A single svg together with several frames is ignored (the animation stays raster).
    fps: playback speed in frames per second (an SWF clip: the SWF frame rate). None = 30.
    Several frames make an animated sprite; they must all have the same size.
    Returns the sprite name.
    """
    p = _proj(project)
    _check_name(name)
    if isinstance(frames, (str, os.PathLike)):
        frames = [frames]
    frames = [str(f) for f in (frames or [])]
    w, h = _png_size(frames[0]) if frames else (width, height)
    for extra in frames[1:]:
        if _png_size(extra) != (w, h):
            raise ValueError(f"Sprite {name!r}: all frames need the same size, {extra} is "
                             f"{_png_size(extra)[0]}x{_png_size(extra)[1]}, expected {w}x{h}")
    svgs = None
    if svg:
        svgs = [str(s) for s in svg] if isinstance(svg, (list, tuple)) else [str(svg)]
        for s in svgs:
            if not os.path.isfile(s):
                raise FileNotFoundError(s)
        if len(svgs) != max(1, len(frames)):
            svgs = None        # no vector version for every frame -> plain PNG animation
    p.sprites[name] = {"frames": frames, "w": w, "h": h, "origin": origin,
                       "svg": svgs, "fps": fps}
    _write_sprite(p, name)
    _write_yyp(p)
    return name
 
 
def gm_create_animated_sprite(name, frames, origin="center", fps=None, svgs=None, project=None):
    """
    One GameMaker sprite with one image per frame (an SWF clip with 7 frames -> 7 images).
    frames: list of equally sized PNG paths, in frame order.
    fps:    playback speed in frames per second (the SWF frame rate); None = 30.
    svgs:   optional list with one .svg per frame (vector sprite); omit for a PNG animation.
    Returns the sprite name.
    """
    frames = [str(f) for f in frames]
    if not frames:
        raise ValueError("gm_create_animated_sprite needs at least one frame")
    return gm_create_sprite(name, frames=frames, origin=origin, svg=svgs, fps=fps, project=project)


# ---- objects ---------------------------------------------------------
def gm_create_object(name, sprite=None, parent=None, visible=True,
                     persistent=False, solid=False, template_events=True, project=None):
    """
    Create an object, optionally with a sprite. Returns the object name.
    template_events: start with the template's Create / Begin Step / Step / Draw events.
    """
    p = _proj(project)
    _check_name(name)
    if sprite and sprite not in p.sprites:
        raise KeyError(f"Sprite {sprite!r} does not exist. Create it first.")
    p.objects[name] = {"sprite": sprite, "parent": parent, "visible": visible,
                       "persistent": persistent, "solid": solid,
                       "events": dict(PLACEHOLDER_EVENTS) if template_events else {}}
    _write_object(p, name)
    _write_yyp(p)
    return name
 
 
def gm_link_object_sprite(obj, sprite, project=None):
    """Assign `sprite` to `obj`. Returns the object name."""
    p = _proj(project)
    if obj not in p.objects:
        raise KeyError(f"Object {obj!r} does not exist.")
    if sprite not in p.sprites:
        raise KeyError(f"Sprite {sprite!r} does not exist.")
    p.objects[obj]["sprite"] = sprite
    _write_object(p, obj)
    return obj
 
 
def gm_add_event(obj, event, code, append=True, project=None):
    """
    Add GML code to an object event.
    event: create, step, begin_step, end_step, draw, draw_gui, destroy, clean_up,
           room_start, room_end, game_start, game_end, alarm0..alarm11,
           'collision:obj_other', or a raw (type, num) tuple.
    """
    p = _proj(project)
    if obj not in p.objects:
        raise KeyError(f"Object {obj!r} does not exist.")
    key = _event_key(event)
    ev = p.objects[obj]["events"]
    if key in ev and append and ev[key] != PLACEHOLDER_EVENTS.get(key):
        ev[key] = ev[key].rstrip() + "\n" + code
    else:
        ev[key] = code  # first real code replaces the template placeholder
    _write_object(p, obj)
    return obj
 
 
def gm_apply_compatibility_objects(transpiled, project=None):
    """Write the AS3 compatibility objects (obj_Sprite, obj_TextField ...) into the project.

    `transpiled` is a transpile() result, a {"compatibility_objects": [...]} dict, or a plain
    list of specs {name, create, step?, draw?}.  They are normal project resources: objects/<name>/
    with Create / Step / Draw files, listed in the .yyp.  Objects that already exist (compared
    without regard to letter case, like Windows) are left untouched.
    Returns the names that were created.
    """
    p = _proj(project)
    specs = transpiled if isinstance(transpiled, list) else transpiled.get("compatibility_objects", [])
    existing = {n.lower() for n in p.objects}
    created = []

    for spec in specs:
        if not isinstance(spec, dict) or "name" not in spec:
            raise ValueError("Each compatibility object must be a dict containing 'name'.")
        name = _check_name(spec["name"])
        if name.lower() in existing:
            continue
        gm_create_object(name, template_events=False, project=project)
        for event in ("create", "step", "draw"):
            if spec.get(event):
                gm_add_event(name, event, spec[event], append=False, project=project)
        existing.add(name.lower())
        created.append(name)

    return created


def gm_apply_transpiled_class(obj, transpiled, project=None):
    """Attach an AS3-to-GML transpile() result to an existing GameMaker object.

    Class results containing Create/Step/Draw events are attached directly to
    this object. MainTimeline Script results are intentionally rejected.
    """
    p = _proj(project)

    if obj not in p.objects:
        raise KeyError(f"Object {obj!r} does not exist.")

    if not isinstance(transpiled, dict):
        raise TypeError("transpiled must be the dict returned by transpile().")

    if transpiled.get("kind") != "object":
        raise ValueError(
            "Expected an AS3 class result (kind='object'); MainTimeline is a script."
        )

    gm_apply_compatibility_objects(transpiled, project=project)

    for event in transpiled.get("events", []):
        event_name = event.get("event")
        if event_name in ("Create", "Step", "Draw"):
            gm_add_event(
                obj,
                event_name.lower(),
                event.get("gml", ""),
                append=False,
                project=project
            )

    return obj


def gm_create_linked_sprite_object(name, frames=None, code=None, width=32, height=32,
                                   origin="center", svg=None, project=None,
                                   template_events=False):
    """Create a sprite and an object with the same SWF instance/linkage name.

    `code` is the dict returned by as3_to_gml.transpile(). Its Create/Step/Draw
    output is attached to the object, making the sprite and its AS3 class a
    single GameMaker resource pair. `name` should come from swflib.sprite_object_map.
    """
    gm_create_sprite(name, frames=frames, width=width, height=height,
                     origin=origin, svg=svg, project=project)
    gm_create_object(name, sprite=name, template_events=template_events, project=project)
    if code is not None:
        gm_apply_transpiled_class(name, code, project=project)
    return name


# ---- rooms -----------------------------------------------------------
def gm_create_room(name, width=1366, height=768, project=None):
    """Create a room. Returns the room name. Rooms run in creation order."""
    p = _proj(project)
    _check_name(name)
    p.rooms[name] = {"w": int(width), "h": int(height), "instances": [], "code": ""}
    if name not in p.room_order:
        p.room_order.append(name)
    _write_room(p, name)
    _write_yyp(p)
    return name
 
 
def gm_set_room_size(room, width, height, project=None):
    p = _proj(project)
    p.rooms[room]["w"], p.rooms[room]["h"] = int(width), int(height)
    _write_room(p, room)
    return room
 
 
def gm_set_room_code(room, code, project=None):
    """Set the room creation code."""
    p = _proj(project)
    p.rooms[room]["code"] = code
    _write_room(p, room)
    return room
 
 
def gm_add_instance(room, obj, x=0, y=0, rotation=0, scale_x=1, scale_y=1,
                    name=None, project=None):
    """Place an object in a room. `name` optionally preserves the SWF instance name."""
    p = _proj(project)
    if room not in p.rooms:
        raise KeyError(f"Room {room!r} does not exist.")
    if obj not in p.objects:
        raise KeyError(f"Object {obj!r} does not exist.")
    iname = _check_name(name) if name else "inst_" + _uid().replace("-", "")[:8].upper()
    p.rooms[room]["instances"].append({"name": iname, "object": obj, "x": x, "y": y,
                                       "rotation": rotation, "scale_x": scale_x,
                                       "scale_y": scale_y})
    _write_room(p, room)
    return iname
 
 
def gm_add_instances(room, placements, project=None):
    """
    Bulk version of gm_add_instance (one disk write).
    placements: iterable of dicts {object, x, y, rotation?, scale_x?, scale_y?}
    """
    p = _proj(project)
    if room not in p.rooms:
        raise KeyError(f"Room {room!r} does not exist.")

    names = []
    for pl in placements:
        if pl["object"] not in p.objects:
            raise KeyError(f"Object {pl['object']!r} does not exist.")
        iname = _check_name(pl["name"]) if pl.get("name") else "inst_" + _uid().replace("-", "")[:8].upper()
        p.rooms[room]["instances"].append({
            "name": iname, "object": pl["object"], "x": pl.get("x", 0), "y": pl.get("y", 0),
            "rotation": pl.get("rotation", 0), "scale_x": pl.get("scale_x", 1),
            "scale_y": pl.get("scale_y", 1)})
        names.append(iname)
    _write_room(p, room)
    return names
 
 
# ---- sounds / scripts ------------------------------------------------
def gm_create_sound(name, file=None, volume=1.0, project=None):
    """
    Import an audio file (.wav/.mp3/.ogg). With no file, a short silent .wav is
    created as a placeholder. Returns the sound name.
    """
    p = _proj(project)
    _check_name(name)
    if file:
        ext = os.path.splitext(file)[1].lower()
        if not os.path.isfile(file):
            raise FileNotFoundError(file)
    else:
        ext = ".wav"
    p.sounds[name] = {"src": str(file) if file else None, "ext": ext, "volume": volume}
    _write_sound(p, name)
    _write_yyp(p)
    return name
 
 
def gm_create_script(name, code="", project=None):
    """Create a GML script resource. Returns the script name."""
    p = _proj(project)
    _check_name(name)
    p.scripts[name] = {"code": code}
    _write_script(p, name)
    _write_yyp(p)
    return name
 
 
# gml_ aliases, matching the names you wrote in your request
gml_create_project = gm_create_project
gml_create_room = gm_create_room
gml_create_object = gm_create_object
gml_create_sprite = gm_create_sprite
gml_link_object_sprite = gm_link_object_sprite
gml_create_sound = gm_create_sound
 
 
if __name__ == "__main__":
    # python gmlib.py [template_folder]   -> shows which template would be used
    searched = []
    found = _find_template(sys.argv[1] if len(sys.argv) > 1 else None, searched)
    print("current folder :", os.getcwd())
    print("gmlib.py folder:", _HERE)
    print("looked in      :")
    for path in searched:
        print("   ", path, "(options/ found)" if _is_template(path) else "")
    if found:
        print("\nTEMPLATE FOUND :", found)
        for folder, _, files in os.walk(os.path.join(found, "options")):
            print("   ", os.path.relpath(folder, found), f"({len(files)} file(s))")
    else:
        print("\nNO TEMPLATE FOUND - nothing would be copied into new projects.")
 