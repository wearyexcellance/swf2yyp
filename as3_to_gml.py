#!/usr/bin/env python3
"""
as3_to_gml.py - ActionScript 3 -> semantic GML lowering (v5)
==============================================================================

Uses a semantic statement IR and a GameMaker-oriented backend.  It is an
interpreter-style lowering pipeline, not a source-line-for-source-line compiler
and not a complete ActionScript virtual machine.

Turns an AS3 class into an "event array":

    [ ("Create", gml), ("Step", gml), ("Draw", gml) ]

...or, when the source is the MAIN class / MAIN TIMELINE / a frame script, into ONE
raw, independent script file: plain GML.  Never an object: no Create, no Step, no Draw.

Mapping rules
-------------
* Constructor, fields, helper methods ............. Create event
* Event listeners (addEventListener) .............. each handler becomes a function
                                                     (defined once in Create) that is
                                                     DISPATCHED from the Step event when
                                                     its trigger fires
* MouseEvent listeners ............................ plain, direct code in Step:
                                                       if (mouse_check_button_pressed(mb_left)) {
                                                           onClick();
                                                       }
* removeEventListener ............................. flips the listener's enable-flag
                                                     (only listeners that are removed keep a flag)
* Timer + TimerEvent.TIMER ........................ small timer struct ticked in Step
* graphics.* / Sprite drawing ..................... Draw event (always starts with draw_self())
* TextField ....................................... struct drawn in Draw with
                                                     draw_set_color(...) + draw_text(...)
* Math.*, trace, Array/String methods, casts ...... GML equivalents
* addChild(new Foo()) / addChildAt(new Foo(), i) .. instance_create_depth(0, 0, 0, obj_Foo)

v5 rules
--------
* classes stay objects (Create/Step/Draw), MainTimeline included; only a class-less frame script
  becomes a script.  Opt in per class with  --main Name  to get one independent script
* MouseEvent listeners -> direct  if (mouse_check_button_...) { handler(); }  in Step
* TextField -> draw_set_alpha / draw_set_color / draw_text in Draw
* the CLI transpiles a whole folder as one project (main-class globals/functions are
  wired into every other class)

v3 rules
--------
* every function is emitted as   function name(args) { ... }
  (never  name = function(args) { ... };)
* GML built-ins are respected (names are renamed name_ / _name when they would clash).
  Extend the list with  --builtins my_names.txt
* main timeline / frame script  ->  ONE independent GML library script (no event files)
* semantic IR pass classifies declarations, assignments, branches, loops, calls,
  returns and drawing operations before optimized GML emission
* generated object Create code orders variables/state before functions and logic
* the Draw event of an object always begins with draw_self()
* `root` is removed:  root.foo -> foo   (a bare `root` -> self)
* AS3 namespaces are removed:  a.motion_internal::spanStart -> a.spanStart
* `self.` / `this.` is never emitted
* addChild / addChildAt of a `new Foo()`  ->  just  instance_create_depth(...)   (no TODO)
* conditions are always compared with ==  ; `x is Foo` -> is_*() / object_index test
* `for each` / `for in` -> classic GML for loops
* obfuscated names:  §name§ -> __name__   (and every stray § -> __)

Usage
-----
    python as3_to_gml.py Main.as                                   # -> ./gml_out/Main/
    python as3_to_gml.py Main.as --location D:/GM/objects --name obj_player
    python as3_to_gml.py src_folder/ -l out --name game            # -> out/game/<Class>/
    python as3_to_gml.py src_folder/ --main MyGameClass            # extra main-class name
    python as3_to_gml.py Main.as --builtins extra_gml_names.txt
    python -c "import as3_to_gml as t; print(t.as3_to_gml(open('Main.as').read())['events'])"

The front-end still uses pragmatic lexical/brace-aware parsing for AS3 syntax;
the semantic IR/backend is not a full AS3 VM or a complete AS3 compiler.
Anything it cannot translate is left in place with a  // TODO  comment and
listed in the warnings.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys

# ============================================================================
# 0. SOURCE CLEAN-UP   (§name§ -> __name__, ns::name -> name, root. -> '')
# ============================================================================

STRING_RE = re.compile(r'"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\'')
CLOSERS = {'(': ')', '[': ']', '{': '}'}

_OBF_PAIR = re.compile(r'§([^§\s()\[\]{};,:+*/=<>!?&|^~"\'.]+)§')


def _deob_chunk(t: str) -> str:
    # §_-1a§  ->  __ + _ _1a + __   (characters that are illegal in a GML name become "_")
    t = _OBF_PAIR.sub(lambda m: '__' + re.sub(r'\W', '_', m.group(1)) + '__', t)
    return t.replace('§', '__')

def _clean_chunk(t: str) -> str:
    """Clean AS3 syntax and convert common MovieClip APIs to GML."""

    # ------------------------------------------------------------------
    # 1. Namespace qualifiers
    # ------------------------------------------------------------------
    t = re.sub(r'(?:[\w$]+|\*)\s*::\s*', '', t)

    # ------------------------------------------------------------------
    # 2. MovieClip timeline controls
    # ------------------------------------------------------------------

    # this.gotoAndStop(x) -> image_index = x - 1; image_speed = 0
    # this.gotoAndPlay(x) -> image_index = x - 1; image_speed = 1
    #
    # AS3 frame numbers start at 1, GML image_index starts at 0.

    def replace_goto(match):
        target = match.group(1) or ""
        method = match.group(2).lower()
        argument = match.group(3).strip()

        speed = "0" if method == "gotoandstop" else "1"

        if target:
            return (
                f"{target}.image_index = ({argument}) - 1; "
                f"{target}.image_speed = {speed}"
            )

        return (
            f"image_index = ({argument}) - 1; "
            f"image_speed = {speed}"
        )

    t = re.sub(
        r'(?<![\w$])(?:(\b[\w$.]+)\s*\.\s*)?'
        r'(gotoAndStop|gotoAndPlay)\s*\(([^()]*)\)',
        replace_goto,
        t,
        flags=re.IGNORECASE
    )

    # ------------------------------------------------------------------
    # 3. Decompiler loop labels
    # ------------------------------------------------------------------

    t = re.sub(
        r'(?<![\w$\.])(break|continue)\s+loop\d*\s*;',
        r'\1;',
        t
    )

    t = re.sub(
        r'(?<![\w$\.:])loop\d+\s*:(?!:)(?=\s*(?:for|while|do|switch|\{))',
        '',
        t
    )

    t = re.sub(
        r'(?<![\w$\.])loop\d+\s*;',
        '',
        t
    )

    # ------------------------------------------------------------------
    # 4. Root references
    # ------------------------------------------------------------------

    t = re.sub(r'(?<![\w$\.])root\s*\.', '', t)
    t = re.sub(r'(?<![\w$])root\b(?!\s*:)', 'self', t)

    return t


def _map_outside_strings(src: str, fn) -> str:
    out, pos = [], 0
    for m in STRING_RE.finditer(src):
        out.append(fn(src[pos:m.start()]))
        out.append(m.group(0))
        pos = m.end()
    out.append(fn(src[pos:]))
    return ''.join(out)


def deobfuscate(src: str) -> str:
    """Replace the § that decompilers / obfuscators put around identifiers with "__"
    (string literals are left alone)."""
    if '§' not in src:
        return src
    return _map_outside_strings(src, _deob_chunk)


def clean_source(src: str) -> str:
    """De-obfuscate, strip `ns::`, strip `root`.  Comments are removed first by the caller."""
    return _map_outside_strings(deobfuscate(src), _clean_chunk)


# ============================================================================
# 1. TEXT UTILITIES  (comments, strings, brackets, call rewriting, statements)
# ============================================================================

def strip_comments(src: str) -> str:
    """Remove // and /* */ comments but keep strings and line numbers."""
    out, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c in '"\'':
            j = skip_string(src, i)
            out.append(src[i:j + 1])
            i = j + 1
        elif src.startswith('//', i):
            j = src.find('\n', i)
            i = n if j == -1 else j
        elif src.startswith('/*', i):
            j = src.find('*/', i + 2)
            j = n if j == -1 else j + 2
            out.append('\n' * src.count('\n', i, j))
            i = j
        else:
            out.append(c)
            i += 1
    return ''.join(out)


def skip_string(s: str, i: int) -> int:
    """s[i] is a quote; return index of the closing quote."""
    q, j, n = s[i], i + 1, len(s)
    while j < n and s[j] != q:
        if s[j] == '\\':
            j += 1
        j += 1
    return j


def find_matching(s: str, i: int) -> int:
    """s[i] is ( [ or {  -> index of the matching closer."""
    o = s[i]
    c = CLOSERS[o]
    d, j, n = 0, i, len(s)
    while j < n:
        ch = s[j]
        if ch in '"\'':
            j = skip_string(s, j)
        elif ch == o:
            d += 1
        elif ch == c:
            d -= 1
            if d == 0:
                return j
        j += 1
    raise ValueError('unbalanced brackets')


def split_args(s: str) -> list:
    """Split a call's argument text on top-level commas."""
    args, d, start, j, n = [], 0, 0, 0, len(s)
    while j < n:
        ch = s[j]
        if ch in '"\'':
            j = skip_string(s, j)
        elif ch in '([{':
            d += 1
        elif ch in ')]}':
            d -= 1
        elif ch == ',' and d == 0:
            args.append(s[start:j].strip())
            start = j + 1
        j += 1
    last = s[start:].strip()
    if last or args:
        args.append(last)
    return args


def replace_calls(code: str, name_pat: str, fn) -> str:
    """
    Find every  <name_pat>( ... )  call (balanced parens, nested calls handled
    inside-out) and replace it with fn(match, args) -> str | None.
    Returning None keeps the call as is (arguments still converted).
    """
    rx = re.compile(r'(?<![\w$])(?:' + name_pat + r')\s*\(')
    out, pos = [], 0
    while True:
        m = rx.search(code, pos)
        if not m:
            out.append(code[pos:])
            break
        op = m.end() - 1
        try:
            cl = find_matching(code, op)
        except ValueError:
            out.append(code[pos:])
            break
        args = [replace_calls(a, name_pat, fn) for a in split_args(code[op + 1:cl])]
        rep = fn(m, args)
        out.append(code[pos:m.start()])
        out.append(code[m.start():op + 1] + ', '.join(args) + ')' if rep is None else rep)
        pos = cl + 1
    return ''.join(out)


def split_statements(body: str) -> list:
    """Split a function body into top-level statements / blocks."""
    chunks, d, start, j, n = [], 0, 0, 0, len(body)
    while j < n:
        ch = body[j]
        if ch in '"\'':
            j = skip_string(body, j)
        elif ch in '([{':
            d += 1
        elif ch in ')]}':
            d -= 1
            if d == 0 and ch == '}':
                k = j + 1
                while k < n and body[k] in ' \t\r\n':
                    k += 1
                if k < n and (body[k] in ';,)' or
                              re.match(r'(else|catch|finally|while)\b', body[k:k + 8])):
                    pass  # statement continues
                else:
                    chunks.append(body[start:j + 1])
                    start = j + 1
        elif ch == ';' and d == 0:
            chunks.append(body[start:j + 1])
            start = j + 1
        j += 1
    if body[start:].strip():
        chunks.append(body[start:])
    merged = []
    for c in chunks:
        if merged and re.match(r'\s*(else|catch|finally)\b', c):
            merged[-1] += c
        else:
            merged.append(c)
    return [c.strip() for c in merged if c.strip() and c.strip() != ';']


def reindent(code: str) -> str:
    """Normalise indentation from brace depth (AS3 indentation is arbitrary)."""
    out, depth = [], 0
    for raw in code.split('\n'):
        line = raw.strip()
        if not line:
            out.append('')
            continue
        bare = STRING_RE.sub('""', line)
        lead = len(bare) - len(bare.lstrip('}])'))
        cur = max(depth - lead, 0)
        out.append('    ' * cur + line)
        depth = max(depth + sum(bare.count(c) for c in '{([') - sum(bare.count(c) for c in '})]'), 0)
    return '\n'.join(out)


def wrap_len_concat(code: str) -> str:
    """"txt" + string_length(x)  ->  "txt" + string(string_length(x))  (GML won't auto-convert)."""
    for m in reversed(list(re.finditer(r'(?<![\w$])(?:string_length|array_length)\(', code))):
        op = m.end() - 1
        try:
            cl = find_matching(code, op)
        except ValueError:
            continue
        before = code[:m.start()].rstrip()
        after = code[cl + 1:].lstrip()
        if re.search(r'__STR\d+__\s*\+$', before) or re.match(r'\+\s*__STR\d+__', after):
            code = code[:m.start()] + 'string(' + code[m.start():cl + 1] + ')' + code[cl + 1:]
    return code


def indent(text: str, n: int = 1) -> str:
    pad = '    ' * n
    return '\n'.join((pad + l if l.strip() else l) for l in text.split('\n'))


def fn_def(name: str, params: str, body: str) -> str:
    """GML function declaration:  function name(params) { body }   (never  name = function() )"""
    return f'function {name}({params}) {{\n{indent(body)}\n}}'


# ============================================================================
# 2. GML BUILT-INS  (names an AS3 identifier must not collide with)
# ============================================================================

GML_KEYWORDS = set('''
all and begin break case catch constructor continue default delete div do else end enum exit
false finally for function global globalvar if macro mod new noone not or other region endregion
repeat return self static switch then throw true try undefined until var while with xor
infinity NaN pi pointer_null pointer_invalid
'''.split())

GML_VARIABLES = set('''
x y id object_index sprite_index image_index image_speed image_alpha image_angle image_blend
image_xscale image_yscale image_number sprite_width sprite_height sprite_xoffset sprite_yoffset
mask_index direction speed hspeed vspeed friction gravity gravity_direction depth visible solid
persistent layer alarm xstart ystart xprevious yprevious bbox_left bbox_right bbox_top bbox_bottom
path_index path_position path_speed path_orientation path_scale path_endaction
timeline_index timeline_position timeline_speed timeline_running timeline_loop
room room_speed room_width room_height room_persistent score health lives
mouse_x mouse_y mouse_button mouse_lastbutton keyboard_key keyboard_lastkey keyboard_lastchar
keyboard_string current_time current_day current_month current_year current_hour current_minute
current_second fps fps_real delta_time view_camera view_visible view_current async_load
event_data event_type event_number event_object working_directory program_directory temp_directory
game_id os_type os_device os_browser os_version argument argument_count application_surface
browser_width browser_height instance_count instance_id cursor_sprite background_color
show_debug_overlay
'''.split())

GML_FUNCTIONS = set('''
abs ceil floor round frac sign sqrt sqr power exp ln log2 log10 logn sin cos tan arcsin arccos
arctan arctan2 degtorad radtodeg dsin dcos dtan max min mean median clamp lerp choose random
random_range irandom irandom_range randomize real string bool int64 ptr ord chr typeof instanceof
method is_real is_string is_array is_struct is_bool is_undefined is_method is_callable is_nan
is_infinity is_numeric is_instanceof show_message show_debug_message show_error show_question
get_string get_integer game_end game_restart game_save game_load sleep exit
string_format string_length string_pos string_copy string_char_at string_upper string_lower
string_replace string_replace_all string_count string_delete string_insert string_repeat
string_trim string_split string_join string_width string_height string_byte_at string_digits
string_letters string_lettersdigits string_ord_at
array_create array_length array_push array_pop array_insert array_delete array_sort array_copy
array_equals array_get array_set array_resize array_concat array_contains array_get_index
array_shuffle array_reverse array_first array_last array_map array_filter array_reduce
array_foreach array_any array_all array_unique
variable_struct_get variable_struct_set variable_struct_exists variable_struct_remove
variable_struct_get_names variable_struct_names_count variable_instance_get variable_instance_set
variable_instance_exists variable_global_get variable_global_set variable_global_exists
instance_create_depth instance_create_depth instance_destroy instance_exists instance_find
instance_number instance_nearest instance_furthest instance_place instance_position instance_change
instance_copy event_perform event_user event_inherited script_execute script_exists
point_distance point_direction point_in_rectangle point_in_circle point_in_triangle
distance_to_point distance_to_object lengthdir_x lengthdir_y angle_difference
move_towards_point move_bounce_all move_bounce_solid move_wrap move_snap move_random
move_contact_solid move_contact_all move_outside_solid move_outside_all
place_free place_empty place_meeting place_snapped position_empty position_meeting
collision_point collision_rectangle collision_circle collision_line collision_ellipse
draw_self draw_sprite draw_sprite_ext draw_text draw_text_ext draw_text_transformed
draw_text_color draw_rectangle draw_circle draw_ellipse draw_line draw_line_width draw_triangle
draw_roundrect draw_roundrect_ext draw_point draw_arrow draw_healthbar draw_set_color
draw_set_colour draw_set_alpha draw_set_font draw_set_halign draw_set_valign draw_get_color
draw_get_alpha draw_clear draw_clear_alpha draw_surface draw_surface_ext draw_sprite_part
draw_sprite_stretched draw_path draw_primitive_begin draw_primitive_end draw_vertex
keyboard_check keyboard_check_pressed keyboard_check_released keyboard_check_direct keyboard_clear
mouse_check_button mouse_check_button_pressed mouse_check_button_released mouse_wheel_up
mouse_wheel_down mouse_clear gamepad_button_check gamepad_axis_value gamepad_is_connected
make_color_rgb make_colour_rgb make_color_hsv make_colour_hsv merge_color merge_colour
color_get_red color_get_green color_get_blue color_get_hue color_get_saturation color_get_value
audio_play_sound audio_stop_sound audio_stop_all audio_pause_sound audio_resume_sound
audio_is_playing audio_sound_gain audio_sound_pitch sprite_exists sprite_get_width
sprite_get_height sprite_get_number sprite_get_name sprite_add sprite_delete
room_goto room_goto_next room_goto_previous room_restart room_exists
layer_create layer_destroy layer_exists layer_get_id layer_set_visible layer_get_visible
layer_get_depth layer_depth surface_create surface_free surface_exists surface_set_target
surface_reset_target camera_create camera_destroy camera_get_active camera_set_view_pos
camera_set_view_size view_get_camera window_set_fullscreen window_get_fullscreen
window_set_caption window_set_size window_get_width window_get_height window_set_cursor
window_center display_get_width display_get_height
ds_list_create ds_list_add ds_list_destroy ds_list_size ds_list_find_value ds_list_delete
ds_list_clear ds_list_insert ds_list_set ds_list_shuffle ds_list_sort ds_map_create ds_map_add
ds_map_destroy ds_map_exists ds_map_find_value ds_map_delete ds_map_size ds_map_set ds_map_clear
ds_grid_create ds_grid_destroy ds_grid_get ds_grid_set ds_grid_width ds_grid_height
ds_stack_create ds_stack_push ds_stack_pop ds_queue_create ds_queue_enqueue ds_queue_dequeue
date_current_datetime date_get_year date_get_month date_get_day date_get_hour date_get_minute
date_get_second date_create_datetime file_exists file_delete json_encode json_decode json_stringify
json_parse buffer_create buffer_delete buffer_read buffer_write buffer_seek buffer_load buffer_save
time_source_create time_source_start time_source_stop time_source_destroy call_later call_cancel
tilemap_get tilemap_set path_start path_end path_add path_delete font_add font_exists
gpu_set_blendmode shader_set shader_reset matrix_set matrix_get matrix_build matrix_multiply
asset_get_index asset_get_type object_get_name object_exists object_get_sprite object_is_ancestor
object_get_parent alarm_get alarm_set get_timer clipboard_set_text clipboard_get_text
'''.split())

EXTRA_BUILTINS: set = set()      # filled by --builtins / load_builtins()


def load_builtins(path: str) -> int:
    """Add more GML names (whitespace / newline separated, '#' comments allowed)."""
    with open(path, encoding='utf-8') as fh:
        for line in fh:
            for tok in line.split('#')[0].split():
                EXTRA_BUILTINS.add(tok)
    return len(EXTRA_BUILTINS)


def is_reserved(n: str) -> bool:
    return (n in GML_KEYWORDS or n in GML_VARIABLES or n in GML_FUNCTIONS or n in EXTRA_BUILTINS
            or re.fullmatch(r'argument\d{1,2}', n) is not None)


def safe_ident(n: str) -> str:
    n = re.sub(r'\W', '_', n) or '_'
    if n[0].isdigit():
        n = '_' + n
    while is_reserved(n):
        n += '_'
    return n


# static AS3 receivers whose members must never be renamed (Math.round, Keyboard.LEFT ...)
STATIC_RECEIVERS = {'Math', 'Keyboard', 'Mouse', 'Array', 'String', 'Number', 'int', 'uint',
                    'TextFieldType', 'TextFieldAutoSize', 'Event', 'KeyboardEvent',
                    'MouseEvent', 'TimerEvent'}


def _innermost_opener(s: str, pos: int) -> str:
    stack = []
    for ch in s[:pos]:
        if ch in '([{':
            stack.append(ch)
        elif ch in ')]}' and stack:
            stack.pop()
    return stack[-1] if stack else ''


def rename_ident(code: str, old: str, new: str, dot: bool = True) -> str:
    """Class-level rename: bare name, this.name and (when dot) obj.name."""
    rx = re.compile(r'(?<![\w$])' + re.escape(old) + r'\b')

    def f(m):
        before = m.string[:m.start()]
        if before.endswith('.'):
            r = re.search(r'([\w$]+)\.$', before)
            r = r.group(1) if r else ''
            if r in ('this', 'self'):
                return new
            if not dot or r in STATIC_RECEIVERS:
                return m.group(0)
        return new

    return rx.sub(f, code)


def rename_local(code: str, old: str, new: str) -> str:
    """Local rename: bare occurrences only (never obj.name, never {name: value} keys)."""
    rx = re.compile(r'(?<![\w$\.])' + re.escape(old) + r'\b')

    def f(m):
        before = m.string[:m.start()].rstrip()
        after = m.string[m.end():].lstrip()
        if (after.startswith(':') and not after.startswith('::') and before[-1:] in ('{', ',')
                and _innermost_opener(m.string, m.start()) == '{'):
            return m.group(0)          # object-literal key
        return new

    return rx.sub(f, code)


# ============================================================================
# 3. CONTEXT + TABLES
# ============================================================================

class Ctx:
    """State shared by all conversion passes for one class."""

    def __init__(self):
        self.class_name = ''
        self.extends = ''
        self.script_mode = False   # main class / main timeline -> raw independent script
        self.types = {}            # identifier -> declared AS3 type
        self.fields = set()
        self.member_names = set()  # method names of the class
        self.promote = set()       # locals turned into instance vars (step -> draw)
        self.textfields = set()
        self.timers = set()
        self.gfx_alias = set()
        self.listeners = []        # registered event listeners
        self.anon_methods = []     # inline function listeners
        self.event_params = set()
        self.used = set()          # helper functions that must be emitted
        self.flags = set()         # misc feature flags
        self.warnings = []
        self.counter = 0
        self.renames = {}          # class-level: AS3 field/method name -> safe GML name
        self.local_map = {}        # per-function: local/param name -> safe GML name
        self.sprites = set()       # AS3 display-object variables
        self.compat_objects = {}   # generated GameMaker compatibility object specs
        self.alias_owner = {}      # "var g = player.graphics"  ->  {'g': 'player'}
        self.uses_origin = False   # any sprite.graphics drawing -> needs per-sprite origin
        self.object_names = {}     # AS3 class name -> GameMaker object name (for "new Foo()")
        self.global_vars = set()   # MainTimeline variables shared across every object
        self.global_functions = {} # MainTimeline function name -> exported global function name
        self.removed_flags = set() # listener flags touched by removeEventListener
        self.timeline_class = False  # a MainTimeline *class*: stays an object, variables become global
        self.self_origin = '0, 0'  # origin for this.graphics: 'x, y' when the class is a Sprite

    def uid(self):
        self.counter += 1
        return self.counter

    def warn(self, msg):
        if msg not in self.warnings:
            self.warnings.append(msg)

    def need(self, *names):
        self.used.update(names)

    def sync_name(self, old: str, new: str):
        """Keep the type tables valid after `old` was renamed to `new`."""
        for tbl in (self.sprites, self.textfields, self.timers, self.gfx_alias, self.fields,
                    self.member_names):
            if old in tbl:
                tbl.add(new)
        if old in self.types:
            self.types[new] = self.types[old]

    def type_of(self, expr: str):
        e = expr.strip()
        if e.startswith('__STR'):
            return 'String'
        e = re.sub(r'^(self|this)\.', '', e)
        if e.endswith('.text'):
            return 'String'
        return self.types.get(e) or self.types.get(e.split('.')[-1])


def ren(ctx: Ctx, n: str) -> str:
    return ctx.renames.get(n, n)


def ren_path(ctx: Ctx, path: str) -> str:
    parts = path.split('.')
    out = [ren(ctx, parts[0])]
    out += [ren(ctx, p) if p not in GML_VARIABLES else p for p in parts[1:]]
    return '.'.join(out)


KEYMAP = {
    'LEFT': 'vk_left', 'RIGHT': 'vk_right', 'UP': 'vk_up', 'DOWN': 'vk_down',
    'SPACE': 'vk_space', 'ENTER': 'vk_enter', 'ESCAPE': 'vk_escape',
    'SHIFT': 'vk_shift', 'CONTROL': 'vk_control', 'TAB': 'vk_tab',
    'BACKSPACE': 'vk_backspace', 'DELETE': 'vk_delete', 'HOME': 'vk_home',
    'END': 'vk_end', 'PAGE_UP': 'vk_pageup', 'PAGE_DOWN': 'vk_pagedown',
    'ALTERNATE': 'vk_alt', 'INSERT': 'vk_insert', 'PAUSE': 'vk_pause',
    'NUMPAD_ADD': 'vk_add', 'NUMPAD_SUBTRACT': 'vk_subtract', 'NUMPAD_MULTIPLY': 'vk_multiply',
    'NUMPAD_DIVIDE': 'vk_divide', 'NUMPAD_DECIMAL': 'vk_decimal', 'NUMPAD_ENTER': 'vk_enter',
    **{f'F{i}': f'vk_f{i}' for i in range(1, 13)},
    **{f'NUMPAD_{i}': f'vk_numpad{i}' for i in range(10)},
}

# AS3 keyCode numbers -> GML key constants.  (AS3 and GML virtual-key codes are the same
# numbers for these keys, but the GML code reads far better as  ord("A")  than as  65.)
KEYCODES = {8: 'vk_backspace', 9: 'vk_tab', 13: 'vk_enter', 16: 'vk_shift', 17: 'vk_control',
            18: 'vk_alt', 19: 'vk_pause', 27: 'vk_escape', 32: 'vk_space', 33: 'vk_pageup',
            34: 'vk_pagedown', 35: 'vk_end', 36: 'vk_home', 37: 'vk_left', 38: 'vk_up',
            39: 'vk_right', 40: 'vk_down', 45: 'vk_insert', 46: 'vk_delete',
            106: 'vk_multiply', 107: 'vk_add', 109: 'vk_subtract', 110: 'vk_decimal',
            111: 'vk_divide'}
KEYCODES.update({n: f'ord("{chr(n)}")' for n in range(48, 58)})          # 0-9
KEYCODES.update({n: f'ord("{chr(n)}")' for n in range(65, 91)})          # A-Z
KEYCODES.update({96 + i: f'vk_numpad{i}' for i in range(10)})            # numpad 0-9
KEYCODES.update({111 + i: f'vk_f{i}' for i in range(1, 13)})             # F1-F12
KEYCODES.update({186: 'ord(";")', 187: 'ord("=")', 188: 'ord(",")', 189: 'ord("-")',
                 190: 'ord(".")', 191: 'ord("/")', 219: 'ord("[")', 221: 'ord("]")'})
_KEYVAR = r'(?:[\w$]+\.)*(?:keyCode|charCode|keyboard_lastkey)'


def key_const(n) -> str:
    """AS3 key code (int) -> GML constant; unknown codes stay numeric."""
    n = int(n)
    return KEYCODES.get(n, str(n))


def source_key_numbers(clean: str) -> list:
    """Every numeric key code the AS3 source compares keyCode / charCode with (==, case N:)."""
    nums = []
    for m in re.finditer(_KEYVAR + r'\s*(?:==|!=)\s*(\d+)', clean):
        nums.append(int(m.group(1)))
    for m in re.finditer(r'(\d+)\s*(?:==|!=)\s*' + _KEYVAR, clean):
        nums.append(int(m.group(1)))
    for m in re.finditer(_KEYVAR + r'\s*(?:<=|>=|<|>)\s*(\d+)', clean):   # ranges: 48..57 / 65..90
        n = int(m.group(1))
        if 48 <= n <= 57:
            nums += list(range(48, 58))
        elif 65 <= n <= 90:
            nums += list(range(65, 91))
    for m in re.finditer(r'(?<![\w$\.])switch\s*\(', clean):
        try:
            cl = find_matching(clean, m.end() - 1)
            rest = clean[cl + 1:].lstrip()
            if re.search(r'keyCode|charCode', clean[m.end():cl]) and rest.startswith('{'):
                nums += [int(x) for x in re.findall(r'(?<![\w$\.])case\s+(\d+)\s*:', rest[:find_matching(rest, 0)])]
        except ValueError:
            pass
    return nums


def convert_keycodes(code: str, ctx=None) -> str:
    """keyCode == 65  ->  keyCode == ord("A");   case 37:  ->  case vk_left:  (inside switch(keyCode))."""
    code = re.sub(r'(' + _KEYVAR + r')\s*(==|!=|<=|>=|<|>)\s*(\d+)\b',
                  lambda m: f'{m.group(1)} {m.group(2)} {key_const(m.group(3))}', code)
    code = re.sub(r'(?<![\w$\.])(\d+)\s*(==|!=|<=|>=|<|>)\s*(' + _KEYVAR + r')\b',
                  lambda m: f'{key_const(m.group(1))} {m.group(2)} {m.group(3)}', code)
    for m in reversed(list(re.finditer(r'(?<![\w$\.])switch\s*\(', code))):
        try:
            cl = find_matching(code, m.end() - 1)
            if not re.search(r'keyCode|charCode|keyboard_lastkey', code[m.end():cl]):
                continue
            rest = code[cl + 1:]
            lead = len(rest) - len(rest.lstrip())
            if not rest.lstrip().startswith('{'):
                continue
            a = cl + 1 + lead
            b = find_matching(code, a)
            body = re.sub(r'(?<![\w$\.])case\s+(\d+)\s*:',
                          lambda c: f'case {key_const(c.group(1))}:', code[a:b])
            code = code[:a] + body + code[b:]
        except ValueError:
            continue
    return code


MATH = {
    'floor': 'floor', 'ceil': 'ceil', 'round': 'round', 'abs': 'abs',
    'sqrt': 'sqrt', 'sin': 'sin', 'cos': 'cos', 'tan': 'tan',
    'atan': 'arctan', 'atan2': 'arctan2', 'asin': 'arcsin', 'acos': 'arccos',
    'pow': 'power', 'max': 'max', 'min': 'min', 'exp': 'exp', 'log': 'ln',
}

PROPS = {
    'rotation': 'image_angle', 'alpha': 'image_alpha',
    'scaleX': 'image_xscale', 'scaleY': 'image_yscale',
    'currentFrame': '(image_index + 1)', 'totalFrames': 'image_number',
    'width': 'sprite_width', 'height': 'sprite_height',
}

EVENT_PARAM_PROPS = {
    # keyCode / charCode / shiftKey / ctrlKey are NOT here - keyboard handlers receive a
    # real event struct built by as3_key_event(), so e.keyCode works exactly like in AS3.
    'stageX': 'mouse_x', 'stageY': 'mouse_y',
    'localX': '(mouse_x - x)', 'localY': '(mouse_y - y)',
    'target': 'id', 'currentTarget': 'id',
    'delta': '(mouse_wheel_up() - mouse_wheel_down())',
}

# AS3 event constant (last token) -> GML trigger condition
EVENT_COND = {
    'ENTER_FRAME': 'true', 'EXIT_FRAME': 'true', 'FRAME_CONSTRUCTED': 'true',
    'KEY_DOWN': 'keyboard_check_pressed(vk_anykey)',
    'KEY_UP': 'keyboard_check_released(vk_anykey)',
    'CLICK': 'mouse_check_button_pressed(mb_left)',
    'MOUSE_DOWN': 'mouse_check_button_pressed(mb_left)',
    'MOUSE_UP': 'mouse_check_button_released(mb_left)',
    'DOUBLE_CLICK': 'mouse_check_button_pressed(mb_left)',
    'RIGHT_CLICK': 'mouse_check_button_pressed(mb_right)',
    'RIGHT_MOUSE_DOWN': 'mouse_check_button_pressed(mb_right)',
    'RIGHT_MOUSE_UP': 'mouse_check_button_released(mb_right)',
    'MIDDLE_CLICK': 'mouse_check_button_pressed(mb_middle)',
    'MOUSE_MOVE': '(mouse_x != __prev_mx || mouse_y != __prev_my)',
    'MOUSE_WHEEL': '(mouse_wheel_up() || mouse_wheel_down())',
    'MOUSE_OVER': 'position_meeting(mouse_x, mouse_y, id)',
    'ROLL_OVER': 'position_meeting(mouse_x, mouse_y, id)',
    'MOUSE_OUT': '!position_meeting(mouse_x, mouse_y, id)',
    'ROLL_OUT': '!position_meeting(mouse_x, mouse_y, id)',
}
ONCE_EVENTS = {'ADDED_TO_STAGE', 'ADDED', 'INIT', 'COMPLETE', 'ACTIVATE'}
MOUSE_EVENTS = {k for k in EVENT_COND if k.startswith(('CLICK', 'MOUSE_', 'ROLL_', 'DOUBLE_', 'RIGHT_', 'MIDDLE_'))}
SPRITE_BASES = {'Sprite', 'MovieClip', 'Bitmap', 'DisplayObject', 'Shape', 'SimpleButton', 'DisplayObjectContainer'}

# `x is Type`  ->  GML type test (types with no GML class fall back to object_index == obj_Type)
IS_TESTS = {
    'Number': 'is_real', 'int': 'is_real', 'uint': 'is_real', 'String': 'is_string',
    'Boolean': 'is_bool', 'Array': 'is_array', 'Function': 'is_method', 'Object': 'is_struct',
    'Point': 'is_struct', 'Rectangle': 'is_struct', 'TextField': 'is_struct',
    'Sprite': 'is_struct', 'Shape': 'is_struct', 'MovieClip': 'is_struct', 'Timer': 'is_struct',
}

# display classes that become plain structs (never GM instances)
PLAIN_DISPLAY = ('Sprite', 'Shape', 'Bitmap', 'SimpleButton')

# Classes listed here become ONE independent GML script instead of an object.
# Empty by default (a class such as MainTimeline stays an object with code).  Opt in with  --main Name
MAIN_CLASS_NAMES = set()   # empty by default: every class stays an object (Create/Step/Draw)
RAW_TOP_LEVEL = False   # --raw : main-script start-up code is emitted as plain top-level GML

# TextField drawing, inlined into Draw (the loop header is written by the assembler)
TEXT_DRAW_BODY = """{
    var _tf = __text_list[__t];
    if (_tf.visible) {
        draw_set_alpha(_tf.alpha);
        if (_tf.background) { draw_set_color(as3_rgb(_tf.backgroundColor)); draw_rectangle(_tf.x, _tf.y, _tf.x + _tf.width, _tf.y + _tf.height, false); }
        if (_tf.border) { draw_set_color(as3_rgb(_tf.borderColor)); draw_rectangle(_tf.x, _tf.y, _tf.x + _tf.width, _tf.y + _tf.height, true); }
        draw_set_color(as3_rgb(_tf.color));
        if (_tf.wordWrap) draw_text_ext(_tf.x, _tf.y, _tf.text, -1, _tf.width);
        else draw_text(_tf.x, _tf.y, _tf.text);
    }
}"""


# AS3 display classes -> GameMaker compatibility objects (obj_Sprite, obj_TextField ...), the
# `default_for` type defaults and instance_create_depth(x, y, -1, obj_...) all live in as3_compat.py
from as3_compat import (COMPAT_DISPLAY_OBJECTS, ALWAYS_COMPAT, compat_type, compat_specs,  # noqa: E402
                        register_compat_object, inst_create, default_for)


# ---- GML helper functions emitted only when used --------------------------
# (always declared as  function name(...) { ... } )
HELPERS = {
    'as3_rgb': ('''function as3_rgb(_c) {
    // AS3 colours are 0xRRGGBB, GML colours are BGR
    return make_color_rgb((_c >> 16) & 255, (_c >> 8) & 255, _c & 255);
}''', []),
    'gfx_reset': ('''function gfx_reset() {
    __filling = false; __line_w = 0; __line_col = c_black; __line_a = 1;
    __fill_col = c_black; __fill_a = 1; __pen_x = 0; __pen_y = 0;
}''', []),
    'gfx_lineStyle': ('''function gfx_lineStyle(_t = 0, _c = 0, _a = 1) {
    __line_w = _t; __line_col = as3_rgb(_c); __line_a = _a;
}''', ['as3_rgb']),
    'gfx_beginFill': ('''function gfx_beginFill(_c = 0, _a = 1) {
    __fill_col = as3_rgb(_c); __fill_a = _a; __filling = true;
}''', ['as3_rgb']),
    'gfx_endFill': ('''function gfx_endFill() {
    __filling = false;
}''', []),
    'gfx_moveTo': ('''function gfx_moveTo(_x, _y) {
    __pen_x = _x; __pen_y = _y;
}''', []),
    'gfx_lineTo': ('''function gfx_lineTo(_x, _y) {
    if (__line_w > 0) {
        draw_set_alpha(__line_a); draw_set_color(__line_col);
        draw_line_width(__pen_x, __pen_y, _x, _y, __line_w);
        draw_set_alpha(1);
    }
    __pen_x = _x; __pen_y = _y;
}''', []),
    'gfx_curveTo': ('''function gfx_curveTo(_cx, _cy, _ax, _ay) {
    // quadratic bezier approximated with 12 segments
    var _x0 = __pen_x, _y0 = __pen_y;
    for (var _i = 1; _i <= 12; _i++) {
        var _t = _i / 12, _u = 1 - _t;
        gfx_lineTo(_u * _u * _x0 + 2 * _u * _t * _cx + _t * _t * _ax,
                   _u * _u * _y0 + 2 * _u * _t * _cy + _t * _t * _ay);
    }
}''', ['gfx_lineTo']),
    'gfx_drawRect': ('''function gfx_drawRect(_x, _y, _w, _h) {
    if (__filling) { draw_set_alpha(__fill_a); draw_set_color(__fill_col); draw_rectangle(_x, _y, _x + _w, _y + _h, false); }
    if (__line_w > 0) { draw_set_alpha(__line_a); draw_set_color(__line_col); draw_rectangle(_x, _y, _x + _w, _y + _h, true); }
    draw_set_alpha(1);
}''', []),
    'gfx_drawRoundRect': ('''function gfx_drawRoundRect(_x, _y, _w, _h, _ew, _eh = undefined) {
    if (is_undefined(_eh)) _eh = _ew;
    if (__filling) { draw_set_alpha(__fill_a); draw_set_color(__fill_col); draw_roundrect_ext(_x, _y, _x + _w, _y + _h, _ew, _eh, false); }
    if (__line_w > 0) { draw_set_alpha(__line_a); draw_set_color(__line_col); draw_roundrect_ext(_x, _y, _x + _w, _y + _h, _ew, _eh, true); }
    draw_set_alpha(1);
}''', []),
    'gfx_drawCircle': ('''function gfx_drawCircle(_x, _y, _r) {
    if (__filling) { draw_set_alpha(__fill_a); draw_set_color(__fill_col); draw_circle(_x, _y, _r, false); }
    if (__line_w > 0) { draw_set_alpha(__line_a); draw_set_color(__line_col); draw_circle(_x, _y, _r, true); }
    draw_set_alpha(1);
}''', []),
    'gfx_drawEllipse': ('''function gfx_drawEllipse(_x, _y, _w, _h) {
    if (__filling) { draw_set_alpha(__fill_a); draw_set_color(__fill_col); draw_ellipse(_x, _y, _x + _w, _y + _h, false); }
    if (__line_w > 0) { draw_set_alpha(__line_a); draw_set_color(__line_col); draw_ellipse(_x, _y, _x + _w, _y + _h, true); }
    draw_set_alpha(1);
}''', []),
    # ---------------- TextField ----------------
    'as3_textfield': ('''function as3_textfield() {
    // stands in for flash.text.TextField
    return { text: "", prevText: "", x: 0, y: 0, width: 100, height: 20,
             color: 0x000000, size: 12, font: "", alpha: 1, visible: true,
             border: false, borderColor: 0x000000,
             background: false, backgroundColor: 0xFFFFFF,
             multiline: false, wordWrap: false, autoSize: "none",
             type: "dynamic", focused: false };
}''', []),
    'as3_addchild': ('''function as3_addchild(_t) {
    if (array_get_index(__text_list, _t) < 0) array_push(__text_list, _t);
}''', []),
    'as3_apply_format': ('''function as3_apply_format(_t, _f) {
    // TextFormat -> TextField
    if (variable_struct_exists(_f, "size"))  _t.size  = _f.size;
    if (variable_struct_exists(_f, "color")) _t.color = _f.color;
    if (variable_struct_exists(_f, "font"))  _t.font  = _f.font;
}''', []),
    'as3_draw_textfield': ('''function as3_draw_textfield(_t) {
    if (!_t.visible) return;
    var _s = _t.size / 12;
    if (_t.autoSize != "none") {
        _t.width  = string_width(_t.text) * _s;
        _t.height = string_height(_t.text) * _s;
    }
    draw_set_alpha(_t.alpha);
    if (_t.background) { draw_set_color(as3_rgb(_t.backgroundColor)); draw_rectangle(_t.x, _t.y, _t.x + _t.width, _t.y + _t.height, false); }
    if (_t.border)     { draw_set_color(as3_rgb(_t.borderColor));     draw_rectangle(_t.x, _t.y, _t.x + _t.width, _t.y + _t.height, true); }
    draw_set_color(as3_rgb(_t.color));
    var _txt = _t.text;
    if (_t.type == "input" && _t.focused && ((current_time div 500) mod 2) == 0) _txt += "|";
    if (_t.wordWrap) draw_text_ext_transformed(_t.x, _t.y, _txt, -1, _t.width / _s, _s, _s, 0);
    else             draw_text_transformed(_t.x, _t.y, _txt, _s, _s, 0);
    draw_set_alpha(1);
}''', ['as3_rgb']),
    'as3_update_textfield': ('''function as3_update_textfield(_t) {
    // TextFieldType.INPUT support: click to focus, then keyboard_string is the text
    if (_t.type != "input" || !_t.visible) return;
    if (mouse_check_button_pressed(mb_left)) {
        var _in = point_in_rectangle(mouse_x, mouse_y, _t.x, _t.y, _t.x + _t.width, _t.y + _t.height);
        if (_in && !_t.focused) keyboard_string = _t.text;
        _t.focused = _in;
    }
    if (_t.focused) _t.text = keyboard_string;
}''', []),
    # ---------------- Timer ----------------
    'as3_timer': ('''function as3_timer(_delay, _repeat = 0) {
    return { delay: _delay, repeatCount: _repeat, running: false, elapsed: 0, count: 0, completed: false };
}''', []),
    'as3_timer_start': ('''function as3_timer_start(_t) {
    _t.running = true; _t.elapsed = 0;
}''', []),
    'as3_timer_stop': ('''function as3_timer_stop(_t) {
    _t.running = false;
}''', []),
    'as3_timer_reset': ('''function as3_timer_reset(_t) {
    _t.running = false; _t.elapsed = 0; _t.count = 0;
}''', []),
    'as3_timer_tick': ('''function as3_timer_tick(_t) {
    if (!_t.running) return false;
    _t.elapsed += delta_time / 1000; // ms
    if (_t.elapsed < _t.delay) return false;
    _t.elapsed -= _t.delay;
    _t.count++;
    if (_t.repeatCount > 0 && _t.count >= _t.repeatCount) { _t.running = false; _t.completed = true; }
    return true;
}''', []),
    'as3_timer_complete': ('''function as3_timer_complete(_t) {
    if (_t.completed) { _t.completed = false; return true; }
    return false;
}''', []),
    # ---------------- Keyboard ----------------
    'as3_key_event': ('''function as3_key_event(_k) {
    // builds the KeyboardEvent that AS3 handlers expect (e.keyCode, e.charCode, e.shiftKey ...)
    return { keyCode: _k, charCode: _k, keyLocation: 0,
             shiftKey: keyboard_check(vk_shift), ctrlKey: keyboard_check(vk_control),
             altKey: keyboard_check(vk_alt) };
}''', []),
    # ---------------- Sprite origin ----------------
    'gfx_origin': ('''function gfx_origin(_x = 0, _y = 0) {
    // every graphics.* call on a Sprite is drawn relative to that Sprite's x / y
    matrix_set(matrix_world, matrix_build(_x, _y, 0, 0, 0, 0, 1, 1, 1));
}''', []),
    'as3_shift': ('''function as3_shift(_a) {
    var _v = _a[0]; array_delete(_a, 0, 1); return _v;
}''', []),
}


# ============================================================================
# 4. PARSING  (package / class / members / script)
# ============================================================================

CLASS_RE = re.compile(
    r'(?:\b(?:public|internal|final|dynamic)\s+)*\bclass\s+(?P<name>\w+)'
    r'(?:\s+extends\s+(?P<ext>[\w\.]+))?(?:\s+implements\s+[\w\.,\s]+)?\s*\{')
METHOD_RE = re.compile(
    r'(?P<mods>(?:\w+\s+)*)function\s+(?:(?P<acc>get|set)\s+)?(?P<name>[\w$]+)\s*'
    r'\((?P<params>[^)]*)\)\s*(?::\s*[\w\.\*<>]+)?\s*$', re.S)
FIELD_RE = re.compile(
    r'^\s*(?P<mods>(?:\w+\s+)*?)(?P<kw>var|const)\s+(?P<name>[\w$]+)\s*'
    r'(?::\s*(?P<type>[\w\.\*]+(?:\.<[\w\.\*]+>)?))?\s*(?:=\s*(?P<init>.*))?$', re.S)
FUNC_LIT_RE = re.compile(r'\bfunction\s*(?P<n>[\w$]*)\s*\((?P<p>[^)]*)\)\s*(?::\s*[\w\.\*<>]+)?\s*\{')


def scan_members(body: str):
    """Walk a class body (depth 0) and return (members, method_spans)."""
    members, spans = [], []
    i, n, start, depth = 0, len(body), 0, 0
    while i < n:
        c = body[i]
        if c in '"\'':
            i = skip_string(body, i)
        elif c in '([':
            depth += 1
        elif c in ')]':
            depth -= 1
        elif c == '{' and depth == 0:
            header = re.sub(r'^\s*(\[[^\]]*\]\s*)+', '', body[start:i])
            m = METHOD_RE.search(header)
            close = find_matching(body, i)
            if m and '=' not in header[:m.start()]:
                mem = dict(kind='method', name=m.group('name'), acc=m.group('acc') or '',
                           params=m.group('params'), body=body[i + 1:close],
                           static='static' in m.group('mods'))
                members.append(mem)
                spans.append((start, close + 1))
                start = close + 1
            i = close
        elif c == ';' and depth == 0:
            header = re.sub(r'^\s*(\[[^\]]*\]\s*)+', '', body[start:i])
            f = FIELD_RE.match(header)
            if f:
                members.append(dict(kind='field', name=f.group('name'), type=f.group('type') or '',
                                    init=(f.group('init') or '').strip(),
                                    static='static' in f.group('mods'),
                                    const=f.group('kw') == 'const'))
            start = i + 1
        i += 1
    return members, spans


def parse_as3(src: str) -> dict:
    """Return {name, extends, fields, methods, ctor, script_mode, main_class, clean}.
    script_mode is True for a main timeline / frame script AND for the main class
    (MAIN_CLASS_NAMES): both become ONE independent script, never an object."""
    src = strip_comments(src)
    src = clean_source(src)                                   # §x§ -> __x__ ; ns:: ; root.
    src = re.sub(r'^\s*import\s+[\w\.\*]+\s*;', '', src, flags=re.M)
    src = re.sub(r'^\s*(?:use\s+namespace\s+\w+|include\s+"[^"]*")\s*;', '', src, flags=re.M)
    inner = src
    pm = re.search(r'\bpackage\b[^{]*\{', src)
    if pm:
        inner = src[pm.end():find_matching(src, pm.end() - 1)]
    cm = CLASS_RE.search(inner)
    if cm:
        body = inner[cm.end():find_matching(inner, cm.end() - 1)]
        members, _ = scan_members(body)
        name, ext = cm.group('name'), (cm.group('ext') or '').split('.')[-1]
        script = name in MAIN_CLASS_NAMES
        ctor_text = None
    else:  # main timeline / frame script
        members, spans = scan_members(inner)
        name, ext, script = 'Script', '', True
        ctor_text = inner
        for a, b in sorted(spans, reverse=True):
            ctor_text = ctor_text[:a] + ctor_text[b:]
    fields = [m for m in members if m['kind'] == 'field']
    methods = [m for m in members if m['kind'] == 'method']
    ctor = None
    for m in list(methods):
        if cm and m['name'] == name:
            ctor = dict(params=m['params'], body=m['body'])
            methods.remove(m)
    if ctor is None:
        ctor = dict(params='', body=ctor_text or '')
    for m in methods:
        if m['acc']:
            m['name'] = f"{m['acc']}_{m['name']}"
    # in a frame script the top-level "var x = ..." lines stay in the script body, so the
    # field list is only used to learn names/types (emitting both would initialise twice)
    return dict(name=name, extends=ext, fields=fields, methods=methods, ctor=ctor,
                script_mode=script, main_class=bool(cm) and script, clean=src,
                emit_fields=not script)


def strip_params(params: str, ctx: Ctx) -> str:
    out = []
    for p in split_args(params):
        m = re.match(r'\s*(\.\.\.)?([\w$]+)\s*(?::\s*[\w\.\*<>]+)?\s*(?:=\s*(.*))?$', p, re.S)
        if not m:
            out.append(p)
            continue
        if m.group(1):
            ctx.warn('rest parameter (...args) is not supported - use an array argument')
        nm = ctx.local_map.get(m.group(2), m.group(2))
        out.append(nm + (f' = {m.group(3).strip()}' if m.group(3) else ''))
    return ', '.join(out)


def collect_types(clean: str, ctx: Ctx, fields):
    for f in fields:
        ctx.fields.add(f['name'])
    for m in re.finditer(r'(?:\b(?:var|const)\s+|[\(,]\s*)([\w$]+)\s*:\s*'
                         r'([A-Z]\w*(?:\.<[\w\.\*]+>)?|int|uint)', clean):
        ctx.types[m.group(1)] = m.group(2)
    for name, t in ctx.types.items():
        if t == 'TextField':
            ctx.textfields.add(name)
        elif t == 'Timer':
            ctx.timers.add(name)
        elif t == 'Graphics':
            ctx.gfx_alias.add(name)
        if t in COMPAT_DISPLAY_OBJECTS:
            register_compat_object(ctx, t)
    for m in re.finditer(r'(?:var\s+)?([\w$]+)\s*(?::\s*\w+)?\s*=\s*[\w\.]*graphics\s*;', clean):
        ctx.gfx_alias.add(m.group(1))
    # Sprite variables (typed, or created with "= new Sprite()")
    ctx.sprites |= {n for n, t in ctx.types.items()
                    if t in ('Sprite', 'Shape', 'MovieClip', 'Bitmap', 'SimpleButton')}
    for m in re.finditer(r'([\w$]+)\s*(?::\s*\w+)?\s*=\s*new\s+(Sprite|Shape|MovieClip|Bitmap|SimpleButton|TextField)\b', clean):
        ctx.sprites.add(m.group(1))
        register_compat_object(ctx, m.group(2))
    for m in re.finditer(r'([\w$]+)\s*(?::\s*\w+)?\s*=\s*([\w$]+)\.graphics\s*;', clean):
        if m.group(2) in ctx.sprites:
            ctx.alias_owner[m.group(1)] = m.group(2)
    ctx.uses_origin = bool(ctx.alias_owner) or any(
        re.search(rf'(?<![\w$\.]){re.escape(s)}\.graphics\b', clean) for s in ctx.sprites)


def collect_keys(clean: str) -> list:
    """Keys the script cares about -> GML key constants (used to poll the keyboard)."""
    keys = []

    def add(k):
        if k not in keys:
            keys.append(k)

    for m in re.finditer(r'\bKeyboard\.(\w+)', clean):
        k = m.group(1)
        if k in KEYMAP:
            add(KEYMAP[k])
        elif re.fullmatch(r'[A-Z]', k):
            add(f'ord("{k}")')
        elif re.fullmatch(r'NUMBER_\d', k):
            add(f'ord("{k[-1]}")')
    for n in source_key_numbers(clean):
        add(key_const(n))        # 65 -> ord("A"), 37 -> vk_left ...
    if not keys:                 # handler reads e.keyCode generically -> watch the usual keys
        keys = ['vk_left', 'vk_right', 'vk_up', 'vk_down', 'vk_space', 'vk_enter', 'vk_escape',
                'vk_shift', 'vk_control'] + [f'ord("{c}")' for c in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789']
    return keys


# ---- GML-name safety --------------------------------------------------------

def build_renames(ctx: Ctx, parsed: dict):
    """Class-level names (fields, methods) that collide with a GML built-in get a trailing _."""
    # MainTimeline fields live in the global namespace, so names such as x/room/score
    # do not collide with instance built-ins and must retain their AS3 spelling.
    names = ([m['name'] for m in parsed['methods']] if (ctx.script_mode or ctx.timeline_class) else
             [f['name'] for f in parsed['fields']] + [m['name'] for m in parsed['methods']])
    taken = set(names)
    for n in names:
        if n in ctx.renames or not is_reserved(n):
            continue
        new = n + '_'
        while is_reserved(new) or new in taken:
            new += '_'
        taken.add(new)
        ctx.renames[n] = new
        ctx.sync_name(n, new)
        ctx.warn(f"'{n}' clashes with a GML built-in - renamed to '{new}'")


def local_renames(params: str, body: str, ctx: Ctx) -> dict:
    """Per-function rename map for parameters and `var`s.
       * names that shadow a field / method  -> _name   (because `this.` is dropped in GML)
       * names that are GML built-ins        -> name_
    """
    names = []
    for p in split_args(params):
        m = re.match(r'\s*(?:\.\.\.)?([\w$]+)', p)
        if m:
            names.append(m.group(1))
    names += re.findall(r'\b(?:var|const)\s+([A-Za-z_$][\w$]*)', body)
    names += re.findall(r'\bcatch\s*\(\s*([\w$]+)', body)
    taken, mapping = set(names), {}
    for n in names:
        if n in mapping:
            continue
        if n in ctx.fields or n in ctx.member_names or n in ctx.global_vars:
            new = '_' + n
        elif is_reserved(n):
            new = n + '_'
            ctx.warn(f"local '{n}' clashes with a GML built-in - renamed to '{new}'")
        else:
            continue
        while new in taken or is_reserved(new):
            new += '_'
        taken.add(new)
        mapping[n] = new
        ctx.sync_name(n, new)
    return mapping


# ============================================================================
# 5. EVENT LISTENERS  (addEventListener -> handler dispatch from Step)
# ============================================================================

def camel_to_const(s: str) -> str:
    return re.sub(r'(?<=[a-z0-9])(?=[A-Z])', '_', s).upper()


def clean_target(t: str):
    t = (t or '').rstrip('.')
    t = re.sub(r'^(this|self)\.?', '', t)
    return None if t in ('', 'stage', 'root') else t


def extract_listeners(code: str, ctx: Ctx) -> str:
    """Replace add/removeEventListener with flag assignments and register them."""

    def reg(m, args):
        if len(args) < 2:
            return None
        ev_raw, hnd = args[0], args[1]
        if STRING_RE.fullmatch(ev_raw):
            event = camel_to_const(ev_raw[1:-1])
        else:
            event = ev_raw.split('.')[-1]
        if hnd.startswith('function'):
            fm = FUNC_LIT_RE.match(hnd)
            if not fm:
                return None
            end = find_matching(hnd, fm.end() - 1)
            name = f'anon_{ctx.uid()}'
            ctx.anon_methods.append(dict(
                name=name, params=fm.group('p'), acc='', static=False, kind='method',
                body=extract_listeners(hnd[fm.end():end], ctx)))
        else:
            name = hnd.split('.')[-1]
        flag = f'__ln_{name}_{event.lower()}'
        return flag, event, name, clean_target(m.group('t'))

    def add(m, args):
        r = reg(m, args)
        if r is None:
            return None
        flag, event, name, target = r
        if not any(l['flag'] == flag for l in ctx.listeners):
            ctx.listeners.append(dict(flag=flag, event=event, handler=name, target=target))
        return f'{flag} = true'

    def rem(m, args):
        r = reg(m, args)
        if r is None:
            return None
        ctx.removed_flags.add(r[0])
        return f'{r[0]} = false'

    pat_t = r'(?P<t>(?:[\w$]+\.)*)'
    code = replace_calls(code, pat_t + 'addEventListener', add)
    code = replace_calls(code, pat_t + 'removeEventListener', rem)
    return code


def strip_flag_sets(code: str, flags) -> str:
    """Mouse listeners are dispatched directly from Step, so their `flag = true` lines go away."""
    for f in flags:
        fl = re.escape(f)
        code = re.sub(r'(?:(?<=[;{}])|\A)\s*' + fl + r'\s*=\s*true\s*;', '', code)
        code = re.sub(r'(?<![\w$])' + fl + r'\s*=\s*true\s*;?', '{}', code)
    return code


def event_condition(ln: dict, ctx: Ctx) -> str:
    ev = ln['event']
    tgt = ren_path(ctx, ln['target']) if ln['target'] else None
    if ev == 'TIMER':
        ctx.need('as3_timer_tick')
        return f'as3_timer_tick({tgt or "timer"})'
    if ev == 'TIMER_COMPLETE':
        ctx.need('as3_timer_complete')
        return f'as3_timer_complete({tgt or "timer"})'
    if ev == 'CHANGE' and tgt:
        return f'{tgt}.text != {tgt}.prevText'
    base = EVENT_COND.get(ev)
    if base is None:
        ctx.warn(f'event {ev} has no GML equivalent - handler {ln["handler"]} never fires (TODO)')
        return 'false'
    if ctx.script_mode and ev in ('MOUSE_OVER', 'ROLL_OVER', 'MOUSE_OUT', 'ROLL_OUT') and not tgt:
        ctx.warn(f'event {ev} needs an instance; a main-timeline script has none - handler never fires (TODO)')
        return 'false'
    if ev == 'MOUSE_MOVE':
        ctx.flags.add('mouse_move')
    if tgt and (ln['target'] in ctx.textfields or ctx.types.get(ln['target']) == 'TextField') and ev in MOUSE_EVENTS:
        hit = f'point_in_rectangle(mouse_x, mouse_y, {tgt}.x, {tgt}.y, {tgt}.x + {tgt}.width, {tgt}.y + {tgt}.height)'
        if ev in ('MOUSE_OVER', 'ROLL_OVER'):
            return hit
        if ev in ('MOUSE_OUT', 'ROLL_OUT'):
            return f'!{hit}'
        return f'({base} && {hit})'
    if tgt and ev in MOUSE_EVENTS:
        return f'{base} /* target: {tgt} */'
    return base


def dispatch_listener(l: dict, H: str, ctx: Ctx) -> str:
    """Step-event code for one listener.  Mouse events are plain, direct checks:
           if (mouse_check_button_pressed(mb_left)) { onClick(); }"""
    cond = event_condition(l, ctx)
    gate = '' if l.get('direct') else f"{l['flag']} && "
    call = f'{H}();' if l['event'] in MOUSE_EVENTS else f'{H}(undefined);'
    return f'if ({gate}{cond}) {{\n    {call}\n}}'


# ============================================================================
# 6. CODE CONVERSION PASSES  (AS3 expression/statement text -> GML text)
# ============================================================================

def gfx_receiver_re(ctx: Ctx) -> str:
    alias = '|'.join(re.escape(a) for a in sorted(ctx.gfx_alias))
    return r'(?:[\w$]+\.)*graphics' + (f'|(?:{alias})' if alias else '')


def uses_gfx(text: str, ctx: Ctx) -> bool:
    return re.search(r'(?<![\w$])(?:' + gfx_receiver_re(ctx) + r')\s*\.', text) is not None


def calls_any(text: str, names) -> bool:
    if not names:
        return False
    return re.search(r'(?<![\w$\.])(?:(?:self|this)\.)?(?:' + '|'.join(map(re.escape, names)) + r')\s*\(', text) is not None


def convert_graphics(code: str, ctx: Ctx) -> str:
    simple = {'clear': 'gfx_reset', 'lineStyle': 'gfx_lineStyle', 'beginFill': 'gfx_beginFill',
              'endFill': 'gfx_endFill', 'moveTo': 'gfx_moveTo', 'lineTo': 'gfx_lineTo',
              'curveTo': 'gfx_curveTo', 'drawRect': 'gfx_drawRect',
              'drawRoundRect': 'gfx_drawRoundRect', 'drawCircle': 'gfx_drawCircle',
              'drawEllipse': 'gfx_drawEllipse'}

    def fn(m, args):
        meth = m.group('m')
        if meth in simple:
            ctx.need(simple[meth])
            return f"{simple[meth]}({', '.join(args)})"
        if meth == 'beginGradientFill' and len(args) >= 2:
            ctx.need('gfx_beginFill')
            ctx.warn('beginGradientFill -> solid fill with first gradient colour')
            return f'gfx_beginFill(({args[1]})[0])'
        if meth in ('lineGradientStyle', 'lineBitmapStyle'):
            return '/* TODO ' + meth + ' */'
        ctx.warn(f'graphics.{meth} is not supported')
        return f"/* TODO graphics.{meth}({', '.join(args)}) */"

    return replace_calls(code, r'(?:' + gfx_receiver_re(ctx) + r')\.(?P<m>\w+)', fn)


def convert_display_calls(code: str, ctx: Ctx) -> str:
    # addChild / addChildAt / removeChild
    def is_display_instance(a):
        return bool(a) and (a in ctx.sprites or
                            ctx.types.get(a.split('.')[-1], '') in COMPAT_DISPLAY_OBJECTS)

    def add_child(m, args):
        a0 = args[0] if args else ''
        if len(args) >= 1 and is_display_instance(a0):
            return f'{a0}.visible = true'
        # addChild(new Foo(..)) / addChildAt(new Foo(..), index): creating the GM instance is
        # all that is needed -> convert_new() turns it into instance_create_depth(...)
        if a0 and re.match(r'new\s+\w', a0):
            return a0
        # addChild(someInstance): it already lives in the room
        if a0 and re.fullmatch(r'[\w$]+(?:\.[\w$]+)*', a0) and \
                ctx.types.get(a0.split('.')[-1], '') not in PLAIN_DISPLAY:
            return f'/* addChild({a0}): instance is already in the room */'
        if a0 and a0.startswith('new '):
            return a0
        return f'/* addChild({a0}) */'

    def rem_child(m, args):
        a0 = args[0] if args else ''
        if is_display_instance(a0):
            return f'{a0}.visible = false'
        if a0 and re.fullmatch(r'[\w$]+(?:\.[\w$]+)*', a0):
            return f'instance_destroy({a0})'
        return f"/* removeChild({', '.join(args)}) */"

    code = replace_calls(code, r'(?:[\w$]+\.)*addChild(?:At)?', add_child)
    code = replace_calls(code, r'(?:[\w$]+\.)*removeChild(?:At)?', rem_child)
    code = re.sub(r'(?<![\w$\.])(?:[\w$]+\.)*numChildren\b', 'instance_count', code)

    # Timer methods
    def timer_m(m, args):
        recv = re.sub(r'^(self|this)\.', '', m.group('r'))
        if recv not in ctx.timers and ctx.types.get(recv.split('.')[-1]) != 'Timer':
            return None
        name = f"as3_timer_{m.group('m')}"
        ctx.need(name)
        return f'{name}({m.group("r")})'

    code = replace_calls(code, r'(?P<r>[\w$\.]+)\.(?P<m>start|stop|reset)', timer_m)

    # TextField helpers
    code = replace_calls(code, r'(?P<r>[\w$\.]+)\.appendText',
                         lambda m, a: f'{m.group("r")}.text += {a[0]}' if a else None)

    def set_fmt(m, args):
        ctx.need('as3_apply_format')
        return f'as3_apply_format({m.group("r")}, {args[0]})' if args else None

    code = replace_calls(code, r'(?P<r>[\w$\.]+)\.setTextFormat', set_fmt)

    def dflt_fmt(m):
        ctx.need('as3_apply_format')
        return f'as3_apply_format({m.group(1)}, {m.group(2).strip()});'

    code = re.sub(r'([\w$\.]+)\.defaultTextFormat\s*=\s*([^;]+);', dflt_fmt, code)
    code = re.sub(r'([\w$\.]+)\.textWidth\b', r'string_width(\1.text)', code)
    code = re.sub(r'([\w$\.]+)\.textHeight\b', r'string_height(\1.text)', code)
    code = re.sub(r'\.htmlText\b', '.text', code)
    code = re.sub(r'\.textColor\b', '.color', code)
    code = re.sub(r'\.currentCount\b', '.count', code)
    code = re.sub(r'\bTextFieldType\.(\w+)', lambda m: f'"{m.group(1).lower()}"', code)
    code = re.sub(r'\bTextFieldAutoSize\.(\w+)', lambda m: f'"{m.group(1).lower()}"', code)
    return code


# ---- loops -------------------------------------------------------------------

FOR_RX = re.compile(r'(?<![\w$\.])for\s+each\s*\(|(?<![\w$\.])for\s*\(')
IN_RE = re.compile(r'\s*(?:var\s+)?([\w$]+)(?:\s*:\s*[\w\.\*]+(?:\.<[\w\.\*]+>)?)?\s+in\s+(.+?)\s*$', re.S)


def convert_loops(code: str, ctx: Ctx) -> str:
    """
    for each (var v:T in expr)   ->  for (var __iN = 0; __iN < array_length(expr); __iN++) { var v = expr[__iN];
    for (var i in array)         ->  for (var i = 0; i < array_length(array); i++)
    for (var k in object)        ->  names = variable_struct_get_names(object); classic loop over names
    Works with brace-less bodies too and with any expression (balanced parentheses).
    """
    out, pos = [], 0
    while True:
        m = FOR_RX.search(code, pos)
        if not m:
            out.append(code[pos:])
            break
        op = m.end() - 1
        try:
            cl = find_matching(code, op)
        except ValueError:
            out.append(code[pos:])
            break
        inner = code[op + 1:cl]
        hm = IN_RE.fullmatch(inner) if ';' not in inner else None
        if not hm:                                   # an ordinary for(;;) loop
            out.append(code[pos:op + 1])
            pos = op + 1
            continue

        is_each = 'each' in m.group(0)
        var, expr = hm.group(1), hm.group(2).strip()
        t = ctx.type_of(expr) or ''
        is_arr = t == 'Array' or t.startswith('Vector')
        is_map = t in ('Object', 'Dictionary')
        k = ctx.uid()
        simple = re.fullmatch(r'[\w$]+(?:\.[\w$]+|\[[^\]]*\])*', expr) is not None
        arr, pre = expr, ''
        if not simple:                               # evaluate a complex expression only once
            arr, pre = f'__a{k}', f'var __a{k} = {expr};\n'

        if is_each and not is_map:                   # for each (v in array)  -> values
            head = f'for (var __i{k} = 0; __i{k} < array_length({arr}); __i{k}++)'
            assign = f'var {var} = {arr}[__i{k}];'
        elif not is_each and is_arr:                 # for (i in array)       -> indices
            head = f'for (var {var} = 0; {var} < array_length({arr}); {var}++)'
            assign = ''
        else:                                        # struct keys (or values for "for each")
            if not is_each and not is_map:
                ctx.warn(f'for ({var} in {expr}): type unknown - assumed Object, looping over struct keys')
            pre = f'var __k{k} = variable_struct_get_names({expr});\n'
            head = f'for (var __j{k} = 0; __j{k} < array_length(__k{k}); __j{k}++)'
            assign = (f'var {var} = {expr}[$ __k{k}[__j{k}]];' if is_each
                      else f'var {var} = __k{k}[__j{k}];')

        rest = code[cl + 1:]
        stripped = rest.lstrip()
        lead = len(rest) - len(stripped)
        out.append(code[pos:m.start()])
        if stripped.startswith('{'):
            out.append(pre + head + ' {' + (' ' + assign if assign else ''))
            pos = cl + 1 + lead + 1                  # continue scanning inside the body
        else:                                        # brace-less body -> wrap the one statement
            chunks = split_statements(stripped)
            st = chunks[0] if chunks else ''
            out.append(pre + head + ' { ' + (assign + ' ' if assign else '') + convert_loops(st, ctx) + ' }')
            pos = cl + 1 + lead + len(st)
    return ''.join(out)


def convert_functions_and_try(code: str, ctx: Ctx) -> str:
    def lit(m):
        # named   -> function name(params) {       anonymous -> function(params) {
        n = m.group('n')
        return f'function {n}({strip_params(m.group("p"), ctx)}) {{' if n \
            else f'function({strip_params(m.group("p"), ctx)}) {{'

    code = FUNC_LIT_RE.sub(lit, code)
    code = re.sub(r'catch\s*\(\s*([\w$]+)\s*:\s*[\w\.]+\s*\)', r'catch (\1)', code)
    code = re.sub(r'\bthrow\s+new\s+\w+\s*\(', 'throw (', code)
    return code


def convert_new(code: str, ctx: Ctx) -> str:
    def fn(m, args):
        c = m.group('c').split('.<')[0].split('.')[-1]
        if m.group('c').startswith('Vector'):
            return f'array_create({args[0]})' if args and args[0] not in ('0', '') else '[]'
        if c == 'Array':
            if not args:
                return '[]'
            if len(args) == 1 and re.fullmatch(r'\d+', args[0]):
                return f'array_create({args[0]})'
            return f"[{', '.join(args)}]"
        if c == 'Object':
            return '{}'
        if c == 'Point':
            return '{x: %s, y: %s}' % ((args + ['0', '0'])[0], (args + ['0', '0'])[1])
        if c == 'Rectangle':
            a = (args + ['0'] * 4)[:4]
            return '{x: %s, y: %s, width: %s, height: %s}' % tuple(a)
        if c in COMPAT_DISPLAY_OBJECTS:
            obj = register_compat_object(ctx, c)
            return inst_create(ctx, obj)
        if c == 'TextFormat':
            keys = ['font', 'size', 'color']
            parts = [f'{k}: {v}' for k, v in zip(keys, args)]
            return '{' + ', '.join(parts) + '}'
        if c == 'Timer':
            ctx.need('as3_timer')
            return f"as3_timer({', '.join(args)})"
        if c == 'Date':
            return 'date_current_datetime()'
        if c == 'Error':
            return args[0] if args else '""'
        if c == 'URLRequest':
            # URLRequest is a Flash wrapper; GML url_open() takes the URL string.
            return args[0] if args else '""'
        obj = ctx.object_names.get(c, f'obj_{c}')
        return inst_create(ctx, obj)

    return replace_calls(code, r'new\s+(?P<c>[\w\.]+(?:\.<[\w\.\*]+>)?)', fn)


def convert_globals(code: str, ctx: Ctx) -> str:
    code = re.sub(r'\s+as\s+[\w\.]+', '', code)            # (x as Foo) -> (x)
    code = re.sub(r'\bMath\.PI\b', 'pi', code)

    def math(m, args):
        f = m.group('f')
        if f == 'random':
            return 'random(1)'
        return f'{MATH[f]}({", ".join(args)})' if f in MATH else None

    code = replace_calls(code, r'Math\.(?P<f>\w+)', math)

    def frame_scripts(m, args):
        # Flash IDE timelines: addFrameScript(0, frame1, 4, frame5 ...).  Frame 1 runs once
        # when the object is created; later frames have no GML equivalent (rooms/state).
        out = []
        for i in range(0, len(args) - 1, 2):
            fn = re.sub(r'^(?:self|this)\.', '', args[i + 1])
            if args[i].strip() == '0':
                out.append(f'{fn}()')
            else:
                out.append(f'/* TODO: frame {args[i]} script {fn} */')
                ctx.warn('addFrameScript for frames after the first is not converted (TODO)')
        return '; '.join(out) or '/* addFrameScript */'

    code = replace_calls(code, r'(?:(?:self|this)\.)?addFrameScript', frame_scripts)

    def navigation(m, args):
        # navigateToURL(new URLRequest(url), target) -> url_open(url)
        # Flash's target-window argument has no direct GameMaker equivalent.
        if not args:
            return '/* TODO: navigateToURL without a URL */'
        return f'url_open({args[0]})'

    code = replace_calls(code, r'(?:(?:flash\.net\.)?navigateToURL)', navigation)

    def glob(m, args):
        f, a = m.group('f'), ', '.join(args)
        if f in ('int', 'uint'):
            return f'floor({a})'
        if f == 'Number':
            return f'real({a})'
        if f == 'String':
            return f'string({a})'
        if f == 'Boolean':
            return f'bool({a})'
        if f == 'parseInt':
            return f'floor(real({args[0]}))'
        if f == 'parseFloat':
            return f'real({a})'
        if f == 'isNaN':
            return f'is_nan({a})'
        if f == 'getTimer':
            return 'current_time'
        if f == 'trace':
            if len(args) <= 1:
                return f'show_debug_message({a})'
            return 'show_debug_message(' + ' + " " + '.join(
                x if x.startswith('__STR') else f'string({x})' for x in args) + ')'
        return None

    code = replace_calls(code, r'(?<!\.)(?P<f>int|uint|Number|String|Boolean|parseInt|parseFloat|isNaN|getTimer|trace)', glob)

    def cast(m, args):
        return args[0] if len(args) == 1 else None

    code = replace_calls(code, r'(?<!\.)(?:MovieClip|Sprite|TextField|DisplayObject|DisplayObjectContainer|Object|Array|Bitmap|Shape|SimpleButton)', cast)
    return code


def convert_collections(code: str, ctx: Ctx) -> str:
    code = re.sub(r'([\w$\.]+)\.length\s*=\s*([^;]+);', r'array_resize(\1, \2);', code)

    def meth(m, args):
        r, f = m.group('r'), m.group('m')
        a = ', '.join(args)
        is_str = ctx.type_of(r) == 'String'
        if f == 'push':
            return f'array_push({r}, {a})'
        if f == 'pop':
            return f'array_pop({r})'
        if f == 'shift':
            ctx.need('as3_shift')
            return f'as3_shift({r})'
        if f == 'unshift':
            return f'array_insert({r}, 0, {a})'
        if f == 'splice':
            if len(args) >= 3 and args[1] == '0':
                return f'array_insert({r}, {args[0]}, {args[2]})'
            return f'array_delete({r}, {args[0]}, {args[1] if len(args) > 1 else "1"})'
        if f == 'indexOf':
            return f'(string_pos({args[0]}, {r}) - 1)' if is_str else f'array_get_index({r}, {args[0]})'
        if f == 'charAt':
            return f'string_char_at({r}, ({args[0]}) + 1)'
        if f == 'toUpperCase':
            return f'string_upper({r})'
        if f == 'toLowerCase':
            return f'string_lower({r})'
        if f == 'substr':
            return f'string_copy({r}, ({args[0]}) + 1, {args[1] if len(args) > 1 else "string_length(" + r + ")"})'
        if f == 'substring':
            end = f'({args[1]}) - ({args[0]})' if len(args) > 1 else f'string_length({r})'
            return f'string_copy({r}, ({args[0]}) + 1, {end})'
        if f == 'split':
            return f'string_split({r}, {a})'
        if f == 'toString':
            return f'string({r})'
        if f == 'toFixed':
            return f'string_format({r}, 0, {a})'
        if f == 'sort':
            return f'array_sort({r}, {a if a and not a.startswith("Array.") else "true"})'
        ctx.warn(f'.{f}() has no automatic GML conversion')
        return None

    code = replace_calls(
        code, r'(?P<r>[\w$]+(?:\.[\w$]+|\[[^\]]*\])*)\.(?P<m>push|pop|shift|unshift|splice|indexOf|charAt|'
              r'toUpperCase|toLowerCase|substr|substring|split|toString|toFixed|sort|join|slice|concat)', meth)

    def length(m):
        r = m.group(1)
        return f'string_length({r})' if ctx.type_of(r) == 'String' else f'array_length({r})'

    code = re.sub(r'(?<![\w$\.])([A-Za-z_][\w$]*(?:\.[A-Za-z_][\w$]*|\[[^\]]*\])*)\.length\b(?!\s*\()',
                  length, code)
    return code


def convert_properties(code: str, ctx: Ctx) -> str:
    # `self.` / `this.` are never emitted: this.x -> x ; a bare `this` -> id (object) / self (script)
    code = re.sub(r'\b(?:this|self)\.', '', code)
    code = re.sub(r'\bthis\b', 'self' if ctx.script_mode else 'id', code)
    if ctx.class_name:
        code = re.sub(rf'\b{re.escape(ctx.class_name)}\.(?=[A-Za-z_])', '', code)  # statics
    code = re.sub(r'(?<![\w$\.])(?:stage\.)?stageWidth\b', 'room_width', code)
    code = re.sub(r'(?<![\w$\.])(?:stage\.)?stageHeight\b', 'room_height', code)
    code = re.sub(r'\bstage\.frameRate\b', 'room_speed', code)
    code = re.sub(r'(?<![\w$\.])(?:stage\.)?mouseX\b', 'mouse_x', code)
    code = re.sub(r'(?<![\w$\.])(?:stage\.)?mouseY\b', 'mouse_y', code)

    def key(m):
        k = m.group(1)
        if k in KEYMAP:
            return KEYMAP[k]
        if re.fullmatch(r'[A-Z]', k):
            return f'ord("{k}")'
        if re.fullmatch(r'NUMBER_\d', k):
            return f'ord("{k[-1]}")'
        ctx.warn(f'Keyboard.{k} has no mapping')
        return m.group(0)

    code = re.sub(r'\bKeyboard\.(\w+)', key, code)
    code = re.sub(r'\bMouse\.hide\s*\(\s*\)', 'window_set_cursor(cr_none)', code)
    code = re.sub(r'\bMouse\.show\s*\(\s*\)', 'window_set_cursor(cr_default)', code)

    ev_params = set(ctx.event_params) | {ctx.local_map.get(p, p) for p in ctx.event_params}
    for p in ev_params:
        code = re.sub(rf'\b{re.escape(p)}\.({"|".join(EVENT_PARAM_PROPS)})\b',
                      lambda m: EVENT_PARAM_PROPS[m.group(1)], code)

    # timeline / MovieClip control  (a method of the same name in the class wins)
    def tl(m, args):
        f = m.group('f')
        if f in ctx.member_names or ren(ctx, f) in ctx.member_names:
            return None
        if ctx.script_mode:
            ctx.warn(f'{f}() is timeline control - not available in an independent script (TODO)')
            return f'/* TODO {f}({", ".join(args)}) */'
        if f == 'gotoAndStop':
            return f'image_index = ({args[0]}) - 1; image_speed = 0'
        if f == 'gotoAndPlay':
            return f'image_index = ({args[0]}) - 1; image_speed = 1'
        if f == 'stop':
            return 'image_speed = 0'
        if f == 'play':
            return 'image_speed = 1'
        if f == 'nextFrame':
            return 'image_index += 1'
        if f == 'prevFrame':
            return 'image_index -= 1'
        return None

    code = replace_calls(code, r'(?<![\w$\.])(?P<f>gotoAndStop|gotoAndPlay|stop|play|nextFrame|prevFrame)', tl)

    if not ctx.script_mode:
        for src_name, gml in PROPS.items():
            if src_name in ctx.types or src_name in ctx.fields or src_name in ctx.local_map:
                continue
            code = re.sub(rf'(?<![\w$\.]){src_name}\b(?!\s*:)(?!\s*=(?!=))', gml, code)
    return code


def strip_declarations(code: str, ctx: Ctx) -> str:
    pat = re.compile(r'\b(?:var|const)\s+([A-Za-z_$][\w$]*)\s*'
                     r'(?::\s*([\w\.\*]+(?:\.<[\w\.\*]+>)?))?(\s*=)?')

    def r(m):
        name, typ, eq = m.group(1), m.group(2), m.group(3)
        prefix = '' if name in ctx.promote else 'var '
        return f'{prefix}{name} =' if eq else f'{prefix}{name} = {default_for(typ, ctx, name)}'

    if re.search(r'\bvar\s+[\w$]+[^;{}()]*,\s*[\w$]+\s*:', code):
        ctx.warn('multiple declarators in one "var a:int, b:int" statement are not converted')
    return pat.sub(r, code)


def _is_test(m, ctx: Ctx) -> str:
    lhs, typ = m.group(1), m.group(2).split('.')[-1]
    if typ in COMPAT_DISPLAY_OBJECTS:
        return f'({lhs}.object_index == {register_compat_object(ctx, typ)})'
    fn = IS_TESTS.get(typ)
    if fn:
        return f'{fn}({lhs})'
    return f'({lhs}.object_index == {ctx.object_names.get(typ, "obj_" + typ)})'


def fix_condition_equals(code: str) -> str:
    """Inside if(...) / while(...) a lone  =  is a comparison in GML too, but we always emit  ==."""
    rx = re.compile(r'(?<![\w$\.])(?:if|while)\s*\(')
    out, pos = [], 0
    while True:
        m = rx.search(code, pos)
        if not m:
            out.append(code[pos:])
            break
        op = m.end() - 1
        try:
            cl = find_matching(code, op)
        except ValueError:
            out.append(code[pos:])
            break
        cond = re.sub(r'(?<![=!<>+\-*/%&|^])=(?!=)', '==', code[op + 1:cl])
        out.append(code[pos:op + 1] + cond)
        pos = cl
    return ''.join(out)


def convert_operators(code: str, ctx: Ctx) -> str:
    code = code.replace('===', '==').replace('!==', '!=')
    code = re.sub(r'\bnull\b', 'undefined', code)
    code = re.sub(r'\bInfinity\b', 'infinity', code)
    code = re.sub(r'\bdelete\s+([\w$\.]+)\.([\w$]+)\s*;', r'variable_struct_remove(\1, "\2");', code)
    # x is Type  ->  type test / object_index ==
    code = re.sub(r'(?<![\w$\.])([A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*|\[[^\]]*\])*)\s+is\s+([A-Za-z_][\w\.]*)',
                  lambda m: _is_test(m, ctx), code)
    L = r'__STR\d+__'
    ident = r'[A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*|\[[^\]]*\])*'
    # "text" + value   -> "text" + string(value)      (GML won't auto-convert numbers)
    code = re.sub(rf'({L})\s*\+\s*({ident})(?=\s*[;,\)\+\]])', r'\1 + string(\2)', code)
    # value + "text"
    code = re.sub(rf'(?<![\w$\.\]\)])(?<!\+ )(?<!- )(?<!\* )(?<!/ )({ident})\s*\+\s*(?={L})',
                  r'string(\1) + ', code)
    # obj["key"] -> obj[$ "key"]
    code = re.sub(rf'(?<=[\w\)\]])\[\s*({L})\s*\]', r'[$ \1]', code)
    code = wrap_len_concat(code)
    code = fix_condition_equals(code)
    return code


# ---------------------------------------------------------------------------
# 6A. SEMANTIC GML IR
# ---------------------------------------------------------------------------
# This is deliberately an intermediate representation rather than a line-for-line
# text replacement stage.  The AS3 front-end first produces semantic statements;
# the GML back-end then emits compact GML idioms.  It is not a complete AS3 VM:
# unsupported language features remain visible as warnings/TODOs.

IR_KINDS = ('declaration', 'assignment', 'branch', 'loop', 'return', 'call', 'draw', 'raw')


def classify_gml_ir(statement: str) -> dict:
    """Classify one already-translated statement into a small semantic IR node."""
    s = statement.strip()
    if not s:
        return {'op': 'empty', 'source': s}
    if re.match(r'^(?:var\s+)?[A-Za-z_$][\w$]*\s*=\s*(?:undefined|false|true|[-+]?\d+(?:\.\d+)?|"(?:\\.|[^"\\])*"|\[\])\s*;?$', s):
        return {'op': 'declaration', 'source': s}
    if re.match(r'^(?:if|switch)\s*\(', s):
        return {'op': 'branch', 'source': s}
    if re.match(r'^(?:for|while|repeat|with)\s*\(', s):
        return {'op': 'loop', 'source': s}
    if re.match(r'^return\b', s):
        return {'op': 'return', 'source': s}
    if re.match(r'^(?:draw_|gfx_|as3_draw)', s):
        return {'op': 'draw', 'source': s}
    if re.match(r'^[\w$.]+\s*(?:\[[^]]+\])?\s*(?:=|\+=|-=|\*=|/=|\+\+|--)', s):
        return {'op': 'assignment', 'source': s}
    if re.match(r'^[\w$.]+\s*\(', s):
        return {'op': 'call', 'source': s}
    return {'op': 'raw', 'source': s}


def optimize_gml_expression(code: str) -> str:
    """Apply semantics-preserving idiom lowering for GameMaker's expression model."""
    # Boolean comparisons are noise in GML and make conditions harder to read.
    code = re.sub(r'\bif\s*\(\s*\(([^()]+)\)\s*==\s*true\s*\)', r'if (\1)', code)
    code = re.sub(r'\bif\s*\(\s*([^()]+?)\s*==\s*true\s*\)', r'if (\1)', code)
    code = re.sub(r'\bif\s*\(\s*([^()]+?)\s*==\s*false\s*\)', r'if (!(\1))', code)
    code = re.sub(r'!\s*!\s*([A-Za-z_$][\w$.]*)', r'\1', code)
    # Turn simple self-referential arithmetic assignments into GML compound ops.
    code = re.sub(r'(?m)^([ \t]*)([A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*)?)\s*=\s*\2\s*\+\s*([^;]+);', r'\1\2 += \3;', code)
    code = re.sub(r'(?m)^([ \t]*)([A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*)?)\s*=\s*\2\s*-\s*([^;]+);', r'\1\2 -= \3;', code)
    code = re.sub(r'(?m)^([ \t]*)([A-Za-z_$][\w$]*(?:\.[A-Za-z_$][\w$]*)?)\s*=\s*\2\s*\*\s*([^;]+);', r'\1\2 *= \3;', code)
    return code


def lower_gml_ir(code: str) -> str:
    """Build a statement IR and emit optimized GML, preserving block boundaries/order."""
    nodes = [classify_gml_ir(x) for x in split_statements(code)]
    emitted = []
    for node in nodes:
        if node['op'] == 'empty':
            continue
        emitted.append(optimize_gml_expression(node['source']))
    return reindent('\n'.join(emitted))


def qualify_global_identifiers(code: str, names) -> str:
    """Qualify known shared identifiers without touching strings, comments or members."""
    names = {n for n in names if re.fullmatch(r"[A-Za-z_$][\w$]*", str(n))}
    if not code or not names:
        return code
    rx = re.compile(r"(?<![\w$.])(" + "|".join(map(re.escape, sorted(names, key=len, reverse=True))) + r")(?![\w$])")
    token = re.compile(r'"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|//[^\n]*|/\*[\s\S]*?\*/')
    out, pos = [], 0
    for m in token.finditer(code):
        out.append(rx.sub(lambda x: "global." + x.group(1), code[pos:m.start()]))
        out.append(m.group(0)); pos = m.end()
    out.append(rx.sub(lambda x: "global." + x.group(1), code[pos:]))
    return "".join(out)


def convert_code(code: str, ctx: Ctx) -> str:
    """Run every conversion pass on an AS3 snippet."""
    strings = []

    def mask(m):
        strings.append(m.group(0))
        return f'__STR{len(strings) - 1}__'

    code = STRING_RE.sub(mask, code)
    code = re.sub(r'\bsuper\s*\([^;]*\)\s*;', '', code)
    for old, new in ctx.local_map.items():           # per-function locals / params
        code = rename_local(code, old, new)
    for old, new in ctx.renames.items():             # class-level names that clash with GML
        code = rename_ident(code, old, new, dot=old not in GML_VARIABLES)
    code = convert_graphics(code, ctx)
    code = convert_display_calls(code, ctx)
    code = convert_loops(code, ctx)
    code = convert_functions_and_try(code, ctx)
    code = convert_new(code, ctx)
    code = convert_sound_calls(code, ctx)
    code = convert_globals(code, ctx)
    code = convert_collections(code, ctx)
    code = convert_properties(code, ctx)
    code = convert_keycodes(code, ctx)
    code = strip_declarations(code, ctx)
    code = convert_operators(code, ctx)
    code = qualify_global_identifiers(code, ctx.global_vars)
    for _src_name, _global_name in ctx.global_functions.items():
        # The timeline transpilation has already renamed its own calls; class
        # transpilation still sees the original AS3 spelling. Handle both forms.
        for _call_name in {_src_name, _global_name}:
            code = re.sub(r'(?<![\w$.])' + re.escape(_call_name) + r'(?=\s*\()',
                          'global.' + _global_name, code)
    code = re.sub(r'(?<![\w$])self\.', '', code)     # safety net: never emit "self."
    code = re.sub(r'(?:[\w$]+|\*)::', '', code)      # safety net: never emit "ns::"
    return re.sub(r'__STR(\d+)__', lambda m: strings[int(m.group(1))], code)


# ============================================================================
# 7. CLASSIFICATION  (what goes to Step, what goes to Draw)
# ============================================================================

def is_alias_decl(stmt: str, ctx: Ctx) -> bool:
    return re.fullmatch(r'\s*(?:var\s+)?[\w$]+\s*(?::\s*\w+)?\s*=\s*[\w\.]*graphics\s*;?\s*', stmt) is not None


def compute_draw_methods(methods, handlers, ctx: Ctx) -> set:
    """Non-handler methods that draw (directly or by calling another drawing method)."""
    D = {m['name'] for m in methods if m['name'] not in handlers and uses_gfx(m['body'], ctx)}
    changed = True
    while changed:
        changed = False
        for m in methods:
            if m['name'] in D or m['name'] in handlers:
                continue
            if calls_any(m['body'], D):
                D.add(m['name'])
                changed = True
    return D


def split_loop(st: str, ctx: Ctx, D: set):
    """A for/for-each/while loop whose body mixes game logic and drawing is cut into
    a logic loop (Step) and a drawing loop (Draw).  Returns (step_loop, draw_loop) or None."""
    m = re.match(r'(?:for\s+each|for|while)\s*\(', st)
    if not m:
        return None
    try:
        cp = find_matching(st, m.end() - 1)
        rest = st[cp + 1:].strip()
        if not (rest.startswith('{') and find_matching(rest, 0) == len(rest) - 1):
            return None
    except ValueError:
        return None
    header, s2, d2 = st[:cp + 1], [], []
    for c in split_statements(rest[1:-1]):
        if is_alias_decl(c, ctx):
            continue
        (d2 if (uses_gfx(c, ctx) or calls_any(c, D)) else s2).append(c)
    if not s2 or not d2:
        return None
    for c in s2:   # a local made in the logic half and read by the drawing half -> keep together
        vm = re.match(r'(?:var|const)\s+([\w$]+)', c)
        if vm and any(re.search(rf'(?<![\w$\.]){re.escape(vm.group(1))}\b', d) for d in d2):
            return None
    return (header + ' {\n' + '\n'.join(s2) + '\n}', header + ' {\n' + '\n'.join(d2) + '\n}')


def split_step_draw(body: str, ctx: Ctx, D: set, script_mode=False):
    """Split statements into (step_chunks, draw_chunks); promote shared locals."""
    step, draw = [], []
    for st in split_statements(body):
        if is_alias_decl(st, ctx):
            continue
        if not (uses_gfx(st, ctx) or calls_any(st, D)):
            step.append(st)
            continue
        parts = split_loop(st, ctx, D)
        if parts:                       # loop mixing logic + drawing -> two loops
            step.append(parts[0])
            draw.append(parts[1])
        else:
            draw.append(st)
    promote = set()
    for st in step:
        m = re.match(r'(?:var|const)\s+([\w$]+)', st)
        if m and (script_mode or any(re.search(rf'(?<![\w$\.]){re.escape(m.group(1))}\b', d) for d in draw)):
            promote.add(m.group(1))
    return step, draw, promote


def chunk_owner(chunk: str, ctx: Ctx):
    """Which Sprite variable does this drawing statement draw on (player.graphics.* ...)?"""
    for m in re.finditer(r'(?<![\w$\.])([\w$]+)\.graphics\b', chunk):
        if m.group(1) in ctx.sprites:
            return m.group(1)
    for alias, owner in ctx.alias_owner.items():
        if re.search(rf'(?<![\w$\.]){re.escape(alias)}\.', chunk):
            return owner
    return None


def conv_chunks(chunks, ctx: Ctx, promote, draw=False) -> str:
    ctx.promote = (set(promote)
                   | {ctx.renames[p] for p in promote if p in ctx.renames}
                   | {ctx.local_map[p] for p in promote if p in ctx.local_map})
    parts, current = [], None          # current = origin set by the previous chunk
    for c in chunks:
        body = lower_gml_ir(convert_code(c, ctx))
        if draw and ctx.uses_origin:
            ctx.need('gfx_origin')
            owner = chunk_owner(c, ctx)
            if owner:   # drawn at the sprite's position, skipped when removeChild()'d
                owner = ren(ctx, owner)
                body = f'if ({owner}.visible) {{\ngfx_origin({owner}.x, {owner}.y);\n{body}\n}}'
                current = None
            elif current != ctx.self_origin:
                body = f'gfx_origin({ctx.self_origin});\n{body}'
                current = ctx.self_origin
        parts.append(body)
    ctx.promote = set()
    return reindent('\n'.join(parts))


# ============================================================================
# 8. ASSEMBLY  (Create / Step / Draw   or   one raw independent script)
# ============================================================================

def helper_block(ctx: Ctx) -> str:
    order, seen = [], set()

    def visit(n):
        if n in seen:
            return
        seen.add(n)
        for d in HELPERS[n][1]:
            visit(d)
        order.append(n)

    for n in sorted(ctx.used):
        visit(n)
    return '\n'.join(HELPERS[n][0] for n in order)


def build_script(name: str, ctx: Ctx, helpers, state, method_defs, create_body,
                 once_calls, step_lines, draw_lines) -> str:
    """Main class / main timeline -> one independent GML library script.

    There are no generated Create/Step/Draw event files.  State/variables are
    emitted first, followed by reusable functions, then the executable
    initialization.  Per-frame and drawing entry points remain callable functions
    in this same script because GameMaker scripts do not own frame events.
    """
    body = [f'// Generated from main class / timeline: {name}',
            '// Single independent GML library script; no event files, no object.',
            '// Call as3_timeline_start() once, as3_timeline_tick() each Step,',
            '// and as3_timeline_draw() from Draw when the source contains drawing.', '']

    # 1. Variables/state first, before any function declarations or executable logic.
    if state:
        body += ['// ---- variables / persistent state', '\n'.join(state), '']

    # 2. Runtime support and source functions.
    if helpers:
        body += ['// ---- runtime helpers', helpers, '']
    if method_defs:
        body += ['// ---- translated source functions', '\n\n'.join(method_defs), '']
    if step_lines:
        body += ['// ---- per-frame logic (same script; call from Step)',
                 fn_def('as3_timeline_tick', '', '\n'.join(step_lines)), '']
    if draw_lines:
        body += ['// ---- drawing logic (same script; call from Draw)',
                 fn_def('as3_timeline_draw', '', '\n'.join(draw_lines)), '']
        ctx.warn('main-script drawing is packaged in as3_timeline_draw() inside the single library script; call it from a Draw event')

    # 3. One-time initialization logic is kept together and emitted last.
    start_lines = []
    if create_body.strip():
        start_lines.append(create_body)
    if once_calls:
        start_lines.extend(once_calls)
    if start_lines and RAW_TOP_LEVEL and ctx.global_functions:
        # raw code runs on load, so the global aliases must exist before it
        body += ['// ---- exported main-script functions (callable from every object)',
                 *[f'global.{e} = {e};' for e in ctx.global_functions.values()], '']
        ctx_aliases_done = True
    else:
        ctx_aliases_done = False
    if start_lines and RAW_TOP_LEVEL:
        body += ['// ---- main timeline code (raw top-level GML, runs when the script loads)', '\n'.join(start_lines), '']
    elif start_lines:
        body += ['// ---- one-time initialization',
                 fn_def('as3_timeline_start', '', '\n'.join(start_lines)), '']
    if step_lines:
        body += ['// ---- optional automatic tick source',
                 'function as3_timeline_enable_auto_tick() {',
                 '    if (!variable_global_exists("as3_timeline_source")) {',
                 '        global.as3_timeline_source = time_source_create(time_source_global, 1, time_source_units_frames, as3_timeline_tick, [], -1);',
                 '        time_source_start(global.as3_timeline_source);',
                 '    }',
                 '}']
    # GML script functions are globally defined by the script asset. Publish explicit
    # global aliases as well, so every other object can call global.<function>().
    if ctx.global_functions and not ctx_aliases_done:
        aliases = [f'global.{exported} = {exported};'
                   for exported in ctx.global_functions.values()]
        body += ['// ---- exported main-script functions (callable from every object)', *aliases]
    return '\n'.join(body).rstrip() + '\n'


# ---- Sound classes ----------------------------------------------------------
SOUND_CLASSES = set()                    # AS3 classes that extend flash.media.Sound
TIMELINE_CLASS_NAMES = {'MainTimeline'}  # classes whose variables become project-wide globals


def prescan_sound_classes(sources) -> None:
    """Register every `class X extends Sound` so other classes know `new X()` plays itself."""
    for src in sources:
        try:
            p = parse_as3(src)
        except Exception:
            continue
        if p['extends'] == 'Sound' and not p['script_mode']:
            SOUND_CLASSES.add(p['name'])


def _prescan_sound_dir(source_dir: str) -> None:
    if not os.path.isdir(source_dir):
        return
    srcs = []
    for fn in sorted(os.listdir(source_dir)):
        if fn.lower().endswith('.as'):
            with open(os.path.join(source_dir, fn), encoding='utf-8-sig', errors='replace') as fh:
                srcs.append(fh.read())
    prescan_sound_classes(srcs)


def sound_object_result(parsed: dict, src: str) -> dict:
    """[Embed(source="x.mp3")] class barrel2 extends Sound  ->  object that plays the sound and dies."""
    cls = parsed['name']
    SOUND_CLASSES.add(cls)
    asset = 'snd_' + re.sub(r'\W', '_', cls)
    em = re.search(r'\[\s*Embed\s*\(\s*source\s*=\s*"([^"]+)"', src)
    note = f'  (embedded: {em.group(1)})' if em else ''
    create = (f'// Sound class "{cls}"{note}\n'
              f'audio_play_sound({asset}, 1, false);\n'
              f'instance_destroy();\n')
    events = [dict(event='Create', file='Create_0.gml', gml=create),
              dict(event='Step', file='Step_0.gml', gml='// (no step logic)\n'),
              dict(event='Draw', file='Draw_0.gml', gml='')]
    return dict(name=cls, kind='object', events=events,
                array=[(e['event'], e['gml']) for e in events], backend='sound',
                compatibility_objects=[], warnings=[], is_sound=True,
                sound_asset=asset, sound_source=em.group(1) if em else '')


def convert_sound_calls(code: str, ctx) -> str:
    """The sound object plays itself on creation, so  x.play(...)  is dropped."""
    if not SOUND_CLASSES:
        return code
    objs = '|'.join(re.escape(ctx.object_names.get(c, f'obj_{c}')) for c in sorted(SOUND_CLASSES))
    code = re.sub(r'(instance_create_depth\([^()]*\b(?:' + objs + r')\b[^()]*\))\s*\.\s*play\s*\([^()]*\)',
                  r'\1', code)

    def var_play(m):
        t = ctx.types.get(m.group(1).split('.')[-1], '')
        if t in SOUND_CLASSES or t == 'Sound':
            return f'/* {m.group(1)}.play(): the sound object plays itself when created */'
        return m.group(0)

    return re.sub(r'(?<![\w$])([\w$]+(?:\.[\w$]+)*)\s*\.\s*play\s*\([^()]*\)', var_play, code)


def transpile(src: str, name_hint: str = 'Main', object_names: dict = None,
              timeline_globals=None, timeline_functions=None) -> dict:
    ctx = Ctx()
    ctx.object_names = dict(object_names or {})
    ctx.global_vars = set(timeline_globals or [])
    ctx.global_functions = dict(timeline_functions or {})
    parsed = parse_as3(src)
    if parsed['extends'] == 'Sound' and not parsed['script_mode']:
        return sound_object_result(parsed, src)
    ctx.script_mode = parsed['script_mode']
    ctx.class_name = parsed['name'] if (parsed.get('main_class') or not ctx.script_mode) else ''
    ctx.extends = parsed['extends']
    ctx.timeline_class = (not ctx.script_mode) and parsed['name'] in TIMELINE_CLASS_NAMES
    if ctx.timeline_class:      # MainTimeline stays an object, its variables are project-wide globals
        ctx.global_vars.update(f['name'] for f in parsed['fields'])
    elif not ctx.script_mode:   # a class' own field shadows a timeline global of the same name
        ctx.global_vars -= {f['name'] for f in parsed['fields']}
    name = (parsed['name'] if parsed.get('main_class') else
            ('main_timeline' if ctx.script_mode else parsed['name']))
    if ctx.script_mode:
        ctx.global_functions = {}
        # Export every main-script method under a collision-resistant, globally callable name.
        for _m in parsed['methods']:
            _original = _m['name']
            _exported = 'as3_timeline_fn_' + safe_ident(_original)
            ctx.renames[_original] = _exported
            ctx.global_functions[_original] = _exported
        ctx.global_vars.update(f['name'] for f in parsed['fields'])
    ctx.clean = parsed['clean']
    collect_types(parsed['clean'], ctx, parsed['fields'])
    for _m in re.finditer(r'([\w$]+)\s*:\s*(\w+)', parsed['clean']):   # vars typed with a Sound class (lowercase names too)
        if _m.group(2) in SOUND_CLASSES:
            ctx.types[_m.group(1)] = _m.group(2)

    methods, ctor = parsed['methods'], parsed['ctor']
    ctx.member_names = {m['name'] for m in methods}
    build_renames(ctx, parsed)

    if ctx.extends in SPRITE_BASES and not ctx.script_mode and uses_gfx(parsed['clean'], ctx):
        # this.graphics.* is relative to the display object -> draw at the instance's x, y
        ctx.uses_origin = True
        ctx.self_origin = 'x, y'

    # -- 1. listeners (also creates anonymous handler methods)
    for m in methods:
        m['body'] = extract_listeners(m['body'], ctx)
    ctor['body'] = extract_listeners(ctor['body'], ctx)
    methods = methods + ctx.anon_methods
    by_name = {m['name']: m for m in methods}
    # MouseEvent listeners: plain `if (mouse_check_button_...) handler();` in Step, no enable-flag
    # (a flag is kept only when removeEventListener is used on that listener)
    for _l in ctx.listeners:
        _l['direct'] = _l['event'] in MOUSE_EVENTS and _l['flag'] not in ctx.removed_flags
    _direct = {_l['flag'] for _l in ctx.listeners if _l['direct']}
    if _direct:
        for _m in methods:
            _m['body'] = strip_flag_sets(_m['body'], _direct)
        ctor['body'] = strip_flag_sets(ctor['body'], _direct)
    handlers = {l['handler'] for l in ctx.listeners}
    for l in ctx.listeners:
        if l['handler'] in by_name:
            first = split_args(by_name[l['handler']]['params'])
            if first:
                ctx.event_params.add(re.split(r'[\s:=]', first[0].strip())[0])
        else:
            ctx.warn(f"listener handler '{l['handler']}' not found in this class")

    # -- 2. classify + convert methods
    D = compute_draw_methods(methods, handlers, ctx)
    method_defs, draw_fns = [], {}
    for m in methods:
        ctx.local_map = local_renames(m['params'], m['body'], ctx)
        params = strip_params(m['params'], ctx)
        fname = ren(ctx, m['name'])
        if m['name'] in handlers:
            step, draw, promote = split_step_draw(m['body'], ctx, D)
            ctx.promote = set()
            if step or not draw:
                body = conv_chunks(step, ctx, promote)
                method_defs.append(fn_def(fname, params, body))
                m['has_step'] = True
            if draw:
                body = conv_chunks(draw, ctx, promote, draw=True)
                method_defs.append(fn_def(fname + '_draw', params, body))
                draw_fns[m['name']] = True
        else:
            body = lower_gml_ir(convert_code(m['body'], ctx))
            method_defs.append(fn_def(fname, params, body))
            m['has_step'] = True
        ctx.local_map = {}

    # -- 3. constructor / script body
    c_step, c_draw, c_promote = split_step_draw(ctor['body'], ctx, D, ctx.script_mode)
    if ctx.script_mode:
        # Top-level var/const declarations become persistent script state,
        # not local declarations buried inside an initialization function.
        _timeline_vars = {f['name'] for f in parsed['fields']}
        c_step = [st for st in c_step if not (re.match(r'\s*(?:var|const)\s+([\w$]+)', st) and
                                               re.match(r'\s*(?:var|const)\s+([\w$]+)', st).group(1) in _timeline_vars)]
    ctx.local_map = {} if ctx.script_mode else local_renames(ctor['params'], ctor['body'], ctx)
    _early_timeline_assignments = []
    create_body = conv_chunks(c_step, ctx, c_promote)
    draw_ctor_body = conv_chunks(c_draw, ctx, c_promote, draw=True)
    if ctx.script_mode and create_body.strip():
        # Promote simple top-level assignments into the script's global
        # initialization block, keeping them ahead of all function declarations.
        _top_assignments, _runtime_lines = [], []
        for _line in split_statements(create_body):
            _m = re.match(r'^\s*(?:global\.)?([A-Za-z_$][\w$]*)\s*(?:\+=|-=|\*=|/=|=)\s*.+;?\s*$', _line, re.S)
            if _m and _m.group(1) in ctx.global_vars:
                _line = re.sub(r'^\s*(?:global\.)?', 'global.', _line)
                _top_assignments.append(_line.rstrip(';') + ';')
            else:
                _runtime_lines.append(_line)
        if _top_assignments:
            _early_timeline_assignments.extend(_top_assignments)
            create_body = '\n'.join(_runtime_lines)
    ctor_param_lines = []
    if not ctx.script_mode:
        for p in split_args(ctor['params']):
            pm = re.match(r'\s*([\w$]+)\s*(?::\s*([\w\.\*]+(?:\.<[\w\.\*]+>)?))?\s*(?:=\s*(.*))?$', p, re.S)
            if not pm:
                continue
            pn = ctx.local_map.get(pm.group(1), pm.group(1))
            dflt = convert_code(pm.group(3), ctx) if pm.group(3) else default_for(pm.group(2), ctx, pm.group(1))
            if not pm.group(3) and pm.group(1) in GML_VARIABLES:
                dflt = pm.group(1)          # ctor(x, y): default to the instance's own x / y
            ctor_param_lines.append(f'{pn} = variable_instance_exists(id, "{pn}") ? {pn} : {dflt};')
    ctx.local_map = {}

    # -- 4. fields
    field_lines = []
    for f in (parsed['fields'] if (parsed['emit_fields'] or ctx.script_mode) else []):
        init = f['init']
        val = convert_code(init, ctx) if init else default_for(f['type'], ctx, f['name'])
        _lhs = ('global.' + ren(ctx, f['name'])) if (ctx.script_mode or ctx.timeline_class) else ren(ctx, f['name'])
        field_lines.append(f"{_lhs} = {val};" + ('  // static' if f['static'] else ''))

    # -- 5. Step event / per-frame dispatch
    step_lines = []
    for l in ctx.listeners:
        if l['event'] in ONCE_EVENTS:
            continue
        H = ren(ctx, l['handler'])
        h = by_name.get(l['handler'])
        if h and h.get('has_step') and l['event'] in ('KEY_DOWN', 'KEY_UP'):
            # One AS3 key event per key that changed state this step.  Polling each key keeps
            # simultaneous keys, key-up and e.keyCode correct (keyboard_lastkey cannot).
            ctx.need('as3_key_event')
            ctx.flags.add('keys')
            chk = 'keyboard_check_pressed' if l['event'] == 'KEY_DOWN' else 'keyboard_check_released'
            step_lines.append(
                f"if ({l['flag']}) {{\n"
                f"    for (var __k = 0; __k < array_length(__keys); __k++) {{\n"
                f"        if ({chk}(__keys[__k])) {H}(as3_key_event(__keys[__k]));\n"
                f"    }}\n}}")
        elif h and h.get('has_step'):
            step_lines.append(dispatch_listener(l, H, ctx))
        elif h is None:
            continue
        elif l['event'] in EVENT_COND and l['event'] != 'ENTER_FRAME':
            ctx.warn(f"handler '{l['handler']}' only draws; its draw code runs every frame while enabled")
    for l in ctx.listeners:
        if l['event'] == 'CHANGE' and l['target']:
            tg = ren_path(ctx, l['target'])
            step_lines.append(f"{tg}.prevText = {tg}.text;")
    if 'mouse_move' in ctx.flags:
        step_lines.append('__prev_mx = mouse_x; __prev_my = mouse_y;')

    # -- 6. Draw event body (everything except the leading draw_self())
    draw_lines = []
    has_gfx = bool(ctx.used & {n for n in HELPERS if n.startswith('gfx_')} or draw_ctor_body or draw_fns)
    if has_gfx:
        draw_lines.append('gfx_reset();')
        ctx.need('gfx_reset')
    if ctx.uses_origin:
        draw_lines.append('gfx_origin(0, 0);')
        ctx.need('gfx_origin')
    if draw_ctor_body:
        draw_lines.append('// ---- drawing code from the AS3 constructor / frame script (redrawn every frame)')
        draw_lines.append(draw_ctor_body)
    for l in ctx.listeners:
        if l['handler'] in draw_fns:
            draw_lines.append(f"{ren(ctx, l['handler'])}_draw();" if l.get('direct') else
                              f"if ({l['flag']}) {ren(ctx, l['handler'])}_draw(undefined);")
    if ctx.uses_origin:
        draw_lines.append('gfx_origin(0, 0);   // back to room coordinates')
    if draw_lines:
        draw_lines.append('draw_set_alpha(1); draw_set_color(c_white);')

    # -- 7. state + once-listeners (shared by both outputs)
    state = list(_early_timeline_assignments)
    if has_gfx:
        state.append('__pen_x = 0; __pen_y = 0; __line_w = 0; __line_col = c_black; __line_a = 1;')
        state.append('__fill_col = c_black; __fill_a = 1; __filling = false;')
    if 'mouse_move' in ctx.flags:
        state.append('__prev_mx = mouse_x; __prev_my = mouse_y;')
    if 'keys' in ctx.flags:
        state.append('__keys = [' + ', '.join(collect_keys(parsed['clean'])) + '];  // keys polled for KEY_DOWN / KEY_UP')
    for l in ctx.listeners:
        if not l.get('direct'):
            state.append(f"{l['flag']} = false;  // {l['event']} -> {ren(ctx, l['handler'])}")
    once_calls = [f"if ({l['flag']}) {ren(ctx, l['handler'])}(undefined);"
                  for l in ctx.listeners if l['event'] in ONCE_EVENTS and l['handler'] in by_name]
    helpers = helper_block(ctx)          # every ctx.need(...) has been made by now
    if ctx.script_mode and field_lines:
        state = field_lines + state

    # -- 8a. main class / main timeline -> one raw independent script (never an object)
    if ctx.script_mode:
        gml = build_script(name, ctx, helpers, state, method_defs, create_body,
                           once_calls, step_lines, draw_lines)
        # a script has no instance: its runtime state lives in global variables
        gml = re.sub(r'(?<![\w.])(__text_list|__keys|__prev_m[xy]|__ln_\w+|__pen_[xy]|__line_(?:w|col|a)|__fill_(?:col|a)|__filling)\b',
                     r'global.\1', gml)
        file = f'{safe_ident(name)}.gml'
        events = [dict(event='Script', file=file, gml=gml)]
        return dict(name=name, kind='script', events=events,
                    array=[('Script', gml)], backend='semantic_gml_ir',
                    compatibility_objects=list(ctx.compat_objects.values()),
                    warnings=ctx.warnings)

    # -- 8b. class -> Create / Step / Draw
    create = [f'// Generated by as3_to_gml.py from "{name}"']
    # Variables and instance state deliberately precede all function declarations.
    if state:
        create += ['', '// ---- state / listener enable-flags', '\n'.join(state)]
    if field_lines:
        create += ['', '// ---- fields', '\n'.join(field_lines)]
    if ctor_param_lines:
        create += ['', '// ---- constructor parameters (pass them in the struct argument of instance_create_depth)',
                   '\n'.join(ctor_param_lines)]
    if helpers:
        create += ['', '// ---- helper functions', helpers]
    if method_defs:
        create += ['', '// ---- methods and event-handler functions', '\n\n'.join(method_defs)]
    if create_body.strip():
        create += ['', '// ---- constructor', create_body]
    if once_calls:
        create += ['', '// ---- ADDED_TO_STAGE-style listeners fire once, right after creation'] + once_calls
    create_text = '\n'.join(create)

    draw_text = ('// Draw event\ndraw_self();\n' + '\n'.join(draw_lines) + '\n') if draw_lines else ''
    events = [
        dict(event='Create', file='Create_0.gml', gml=create_text + '\n'),
        dict(event='Step', file='Step_0.gml',
             gml=('// Step event: event-listener dispatch\n' + '\n'.join(step_lines) + '\n') if step_lines
             else '// (no step logic)\n'),
        dict(event='Draw', file='Draw_0.gml', gml=draw_text),
    ]
    return dict(name=name, kind='object', events=events,
                array=[(e['event'], e['gml']) for e in events],
                backend='semantic_gml_ir',
                compatibility_objects=list(ctx.compat_objects.values()),
                warnings=ctx.warnings)


def as3_to_gml(src: str, name_hint: str = 'Main', object_names: dict = None,
               timeline_globals=None, timeline_functions=None) -> dict:
    """Public entry point: AS3 source -> {'name', 'kind', 'events', 'array', 'warnings'}.
    kind is 'object' (Create/Step/Draw) or 'script' (main class / main timeline: one raw
    independent script).
    object_names maps AS3 linkage/class names to GameMaker object names. When
    paired with swflib.sprite_class_map(info), sprite classes and `new Foo()`
    references resolve to the corresponding SWF-named GameMaker object.
    """
    return transpile(src, name_hint, object_names, timeline_globals, timeline_functions)


def transpile_project_sources(sources: dict, object_names: dict = None) -> dict:
    """Transpile a source set with main-script shared globals/functions wired into classes.

    `sources` maps AS3 class names (or `main_timeline`) to source strings. The main class /
    timeline is processed first; its variables and methods are then qualified in every other
    class.  Returns {source_key: transpile_result}.  The main class / timeline is always a
    script resource, never an object resource.
    """
    sources = dict(sources or {})
    prescan_sound_classes(sources.values())
    timeline_key = next((k for k, v in sources.items() if parse_as3(v)['script_mode']), None)
    results = {}
    globals_, functions_ = set(), {}
    if timeline_key is not None:
        timeline = transpile(sources[timeline_key], 'main_timeline', object_names)
        results[timeline_key] = timeline
        parsed_timeline = parse_as3(sources[timeline_key])
        globals_ = {f['name'] for f in parsed_timeline['fields']}
        functions_ = {m['name']: 'as3_timeline_fn_' + safe_ident(m['name'])
                      for m in parsed_timeline['methods']}
    for _v in sources.values():      # a MainTimeline class: its variables are global for every class
        _p = parse_as3(_v)
        if _p['name'] in TIMELINE_CLASS_NAMES and not _p['script_mode']:
            globals_ = globals_ | {f['name'] for f in _p['fields']}
    for key, source in sources.items():
        if key == timeline_key:
            continue
        results[key] = transpile(source, key, object_names, globals_, functions_)
    return results


def transpile_linked_sprite_classes(source_dir: str, class_to_object: dict) -> dict:
    """Transpile exported AS3 classes and associate each class with its SWF sprite object.

    `class_to_object` is the mapping returned by `swflib.sprite_class_map(info)`.
    The result is {gml_object_name: transpile_result}. Unmatched classes are
    skipped rather than accidentally attached to the wrong sprite.
    """
    linked = {}
    _prescan_sound_dir(source_dir)
    if not os.path.isdir(source_dir):
        raise NotADirectoryError(source_dir)
    for filename in sorted(os.listdir(source_dir)):
        if not filename.lower().endswith('.as'):
            continue
        path = os.path.join(source_dir, filename)
        with open(path, 'r', encoding='utf-8-sig', errors='replace') as fh:
            source = fh.read()
        parsed = parse_as3(source)
        if parsed.get('script_mode'):
            continue
        class_name = parsed.get('name', '')
        short_name = class_name.split('.')[-1]
        object_name = class_to_object.get(class_name) or class_to_object.get(short_name)
        if not object_name:
            continue
        result = transpile(source, name_hint=object_name, object_names=class_to_object)
        result['object_name'] = object_name
        result['as3_class'] = class_name
        linked[object_name] = result
    return linked


# ============================================================================
# 9. CLI
# ============================================================================

def write_result(res: dict, outdir: str):
    os.makedirs(outdir, exist_ok=True)
    for e in res['events']:
        with open(os.path.join(outdir, e['file']), 'w', encoding='utf-8') as fh:
            fh.write(e['gml'])
    with open(os.path.join(outdir, f"{res['name']}_events.json"), 'w', encoding='utf-8') as fh:
        json.dump([dict(event=e['event'], gml=e['gml']) for e in res['events']], fh, indent=2)


def export_gml(res: dict, location: str = 'gml_out', name: str = None) -> str:
    """Write the .gml file(s) (+ json) to  <location>/<name>/.
    name defaults to the AS3 class name.  Returns the absolute folder path."""
    base = os.path.abspath(os.path.expanduser(location))
    outdir = os.path.join(base, name or res['name'])
    write_result(res, outdir)
    return outdir


def main(argv=None):
    ap = argparse.ArgumentParser(
        description='AS3 -> GML.  Classes become Create/Step/Draw objects; the main class / '
                    'main timeline becomes ONE independent GML script.',
        epilog='example:  python as3_to_gml.py src/ --location ~/Projects/MyGame/objects --name game')
    ap.add_argument('input', help='an .as file or a folder of .as files')
    ap.add_argument('-l', '--location', '-o', '--out', dest='location', default='gml_out',
                    help='export parent directory (default ./gml_out)')
    ap.add_argument('-n', '--name', default=None, help='export folder name inside --location')
    ap.add_argument('--builtins', default=None, help='text file with extra GML names')
    ap.add_argument('--main', action='append', default=[],
                    help='extra class name to treat as a MAIN class (single independent script); repeatable')
    ap.add_argument('--timeline', action='append', default=[],
                    help='extra main-timeline class name whose variables become project-wide globals; repeatable')
    ap.add_argument('--raw', action='store_true',
                    help='emit main timeline / main class start-up code as raw top-level GML (no as3_timeline_start wrapper)')
    ap.add_argument('--print', action='store_true', help='also print the result')
    a = ap.parse_args(argv)
    global RAW_TOP_LEVEL
    RAW_TOP_LEVEL = a.raw

    if a.builtins:
        print(f'[builtins] {load_builtins(a.builtins)} extra names loaded')
    MAIN_CLASS_NAMES.update(a.main)
    TIMELINE_CLASS_NAMES.update(a.timeline)

    files = []
    if os.path.isdir(a.input):
        for root_dir, _, fs in os.walk(a.input):
            files += [os.path.join(root_dir, f) for f in fs if f.endswith('.as')]
    else:
        files = [a.input]

    sources, paths = {}, {}
    for path in files:
        key = os.path.splitext(os.path.relpath(path, a.input if os.path.isdir(a.input) else os.path.dirname(path) or '.'))[0]
        with open(path, encoding='utf-8-sig', errors='replace') as fh:
            sources[key] = fh.read()
        paths[key] = path

    # one project pass: main-class / timeline globals + functions are wired into every class
    results = transpile_project_sources(sources)
    for key, res in results.items():
        if len(files) > 1:
            outdir = export_gml(res, os.path.join(a.location, a.name) if a.name else a.location)
        else:
            outdir = export_gml(res, a.location, a.name)
        print(f"[ok] {paths.get(key, key)} -> {outdir}  ({res['name']}, {res['kind']})")
        for w in res['warnings']:
            print(f'     warning: {w}')
        if a.print:
            for ev, gml in res['array']:
                print(f'\n===== {ev} =====\n{gml}')


if __name__ == '__main__':
    main()
