"""Compile shipped custom GLSL with Mesa GLES; this is not browser/visual QA.

No Python OpenGL packages or display server are required. Three's ES 1.00
ShaderMaterial declarations are adapted to the equivalent GLSL ES 3.00
prefix used by its WebGL 2 renderer. Native compiler/linker results do not
establish browser driver compatibility, runtime uniform values, or appearance.
"""
from __future__ import annotations
import ctypes as C
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
WEB = ROOT / 'web/integral-families'


def shader_pairs():
    # Instantiate the actual effects with Three, rather than copying GLSL into
    # the test. Use the application's already installed esbuild/Three packages.
    js = r'''
const fs=require('node:fs'),path=require('node:path');
const root=process.cwd(),web=path.join(root,'web/integral-families');
const resolve=id=>require.resolve(id,{paths:[web,path.join(root,'desktop/explorer')]});
const {build}=require(resolve('esbuild'));
const threeModule=path.join(path.dirname(resolve('three')),'three.module.js');
(async()=>{
const result=await build({stdin:{contents:`import * as THREE from 'three';import {createResonanceEffects} from './resonance-effects.js';export function collect(){const nodes=Array.from({length:5},()=>({visual:new THREE.Group()}));createResonanceEffects({nodes});const pairs=[];for(const n of nodes)n.visual.traverse(o=>{if(o.material?.isShaderMaterial)pairs.push({vertex:o.material.vertexShader,fragment:o.material.fragmentShader});});return pairs;}`,resolveDir:web},bundle:true,write:false,format:'cjs',platform:'node',logLevel:'silent',plugins:[{name:'dependencies',setup(b){b.onResolve({filter:/^three(?:\/.*)?$/},a=>({path:a.path==='three'?threeModule:resolve(a.path)}));}}]});
const m={exports:{}};new Function('module','exports','require',result.outputFiles[0].text)(m,m.exports,require);process.stdout.write(JSON.stringify(m.exports.collect()));
})().catch(e=>{process.stderr.write(String(e));process.exit(1)});
'''
    effects = json.loads(subprocess.check_output(['node', '-e', js], cwd=ROOT, text=True))
    unique = {(p['vertex'], p['fragment']) for p in effects}
    result = [(f'effects-{i + 1}', v, f) for i, (v, f) in enumerate(sorted(unique))]
    assert len(result) == 2, 'Expected surface and filament ShaderMaterial pairs'

    # Scene shader bodies are private closures; read their shipped literals.
    # Fail if new template interpolations cannot be resolved faithfully.
    source = (WEB / 'resonance-scene.js').read_text()
    literal = r"(?:`[^`]*`|'(?:[^'\\]|\\.)*')"
    warp = re.search(r"const warp = ('[^']*');", source).group(1)[1:-1]
    def unpack(text):
        text = text[1:-1].replace('${warp}', warp)
        assert '${' not in text, 'Unresolved shader template interpolation'
        return text
    matches = re.findall(r'vertexShader:\s*(' + literal + r'),\s*fragmentShader:\s*(' + literal + r')', source)
    assert len(matches) == 4, 'Scene shader layout changed: update extraction explicitly'
    for i, (v, f) in enumerate(matches):
        result.append((f'scene-literal-{i + 1}', unpack(v), unpack(f)))
    pv = unpack(re.search(r'const pointVertex = (' + literal + r');', source).group(1))
    pf = unpack(re.search(r'const pointFragment = (' + literal + r');', source).group(1))
    result.append(('scene-points', pv, pf))
    warped = pv.replace('vec4 mv=modelViewMatrix*vec4(position,1.);', warp + ' vec4 mv=modelViewMatrix*vec4(p,1.);')
    assert warped != pv
    result.append(('scene-warped-points', warped, pf))
    return result


class NativeGLES:
    def __init__(self):
        self.egl = C.CDLL('libEGL.so.1')
        self.egl.eglGetProcAddress.restype = C.c_void_p
        self.egl.eglGetProcAddress.argtypes = [C.c_char_p]
        self.display = self.context = self.surface = None
        get_display = self.function('eglGetPlatformDisplayEXT', C.c_void_p, C.c_uint, C.c_void_p, C.POINTER(C.c_int))
        self.display = get_display(0x31DD, None, None)  # EGL_PLATFORM_SURFACELESS_MESA
        initialize = self.function('eglInitialize', C.c_uint, C.c_void_p, C.POINTER(C.c_int), C.POINTER(C.c_int))
        major, minor = C.c_int(), C.c_int()
        if not self.display or not initialize(self.display, C.byref(major), C.byref(minor)):
            raise RuntimeError('Surfaceless EGL initialization is unavailable')
        bind = self.function('eglBindAPI', C.c_uint, C.c_uint)
        if not bind(0x30A0):
            raise RuntimeError('EGL OpenGL ES API is unavailable')
        attrs = (C.c_int * 11)(0x3033, 1, 0x3040, 0x40, 0x3024, 8, 0x3023, 8, 0x3022, 8, 0x3038)
        choose = self.function('eglChooseConfig', C.c_uint, C.c_void_p, C.POINTER(C.c_int), C.POINTER(C.c_void_p), C.c_int, C.POINTER(C.c_int))
        config, count = C.c_void_p(), C.c_int()
        if not choose(self.display, attrs, C.byref(config), 1, C.byref(count)) or count.value != 1:
            raise RuntimeError('No EGL GLES 3 configuration')
        context_attrs = (C.c_int * 3)(0x3098, 3, 0x3038)
        create = self.function('eglCreateContext', C.c_void_p, C.c_void_p, C.c_void_p, C.c_void_p, C.POINTER(C.c_int))
        self.context = create(self.display, config, None, context_attrs)
        pbuffer_attrs = (C.c_int * 5)(0x3057, 1, 0x3056, 1, 0x3038)
        self.surface = self.function('eglCreatePbufferSurface', C.c_void_p, C.c_void_p, C.c_void_p, C.POINTER(C.c_int))(self.display, config, pbuffer_attrs)
        current = self.function('eglMakeCurrent', C.c_uint, C.c_void_p, C.c_void_p, C.c_void_p, C.c_void_p)
        if not self.context or not self.surface or not current(self.display, self.surface, self.surface, self.context):
            raise RuntimeError('EGL GLES context could not be made current')
        get_string = self.function('glGetString', C.c_char_p, C.c_uint)
        self.driver = {k: get_string(v).decode() for k, v in [('vendor', 0x1F00), ('renderer', 0x1F01), ('version', 0x1F02), ('glsl', 0x8B8C)]}

    def function(self, name, result, *args):
        ptr = self.egl.eglGetProcAddress(name.encode())
        if not ptr:
            raise RuntimeError(f'Native entry point {name} unavailable')
        return C.CFUNCTYPE(result, *args)(ptr)

    def compile(self, source, stage):
        create = self.function('glCreateShader', C.c_uint, C.c_uint)
        shader = create(stage)
        encoded = source.encode()
        strings = (C.c_char_p * 1)(encoded)
        self.function('glShaderSource', None, C.c_uint, C.c_int, C.POINTER(C.c_char_p), C.POINTER(C.c_int))(shader, 1, strings, None)
        self.function('glCompileShader', None, C.c_uint)(shader)
        status = C.c_int()
        self.function('glGetShaderiv', None, C.c_uint, C.c_uint, C.POINTER(C.c_int))(shader, 0x8B81, C.byref(status))
        if not status.value:
            buf = C.create_string_buffer(32768)
            self.function('glGetShaderInfoLog', None, C.c_uint, C.c_int, C.POINTER(C.c_int), C.c_char_p)(shader, len(buf), None, buf)
            raise AssertionError(buf.value.decode())
        return shader

    def link(self, vertex, fragment):
        vs, fs = self.compile(adapt(vertex, True), 0x8B31), self.compile(adapt(fragment, False), 0x8B30)
        program = self.function('glCreateProgram', C.c_uint)()
        attach = self.function('glAttachShader', None, C.c_uint, C.c_uint)
        attach(program, vs); attach(program, fs)
        self.function('glLinkProgram', None, C.c_uint)(program)
        status = C.c_int()
        self.function('glGetProgramiv', None, C.c_uint, C.c_uint, C.POINTER(C.c_int))(program, 0x8B82, C.byref(status))
        if not status.value:
            buf = C.create_string_buffer(32768)
            self.function('glGetProgramInfoLog', None, C.c_uint, C.c_int, C.POINTER(C.c_int), C.c_char_p)(program, len(buf), None, buf)
            raise AssertionError(buf.value.decode())
        self.function('glDeleteProgram', None, C.c_uint)(program)
        delete = self.function('glDeleteShader', None, C.c_uint)
        delete(vs); delete(fs)

    def close(self):
        if self.display:
            self.function('eglMakeCurrent', C.c_uint, C.c_void_p, C.c_void_p, C.c_void_p, C.c_void_p)(self.display, None, None, None)
            if self.surface:
                self.function('eglDestroySurface', C.c_uint, C.c_void_p, C.c_void_p)(self.display, self.surface)
            if self.context:
                self.function('eglDestroyContext', C.c_uint, C.c_void_p, C.c_void_p)(self.display, self.context)
            self.function('eglTerminate', C.c_uint, C.c_void_p)(self.display)
            self.display = None


def adapt(source, vertex):
    prefix = '#version 300 es\nprecision highp float;\nprecision highp int;\n'
    source = re.sub(r'\battribute\b', 'in', source)
    source = re.sub(r'\bvarying\b', 'out' if vertex else 'in', source)
    if vertex:
        prefix += 'uniform mat4 modelViewMatrix,projectionMatrix;\nuniform mat3 normalMatrix;\nin vec3 position,normal,color;\nin vec2 uv;\n'
    else:
        prefix += 'out vec4 pc_fragColor;\n'
        source = re.sub(r'\bgl_FragColor\b', 'pc_fragColor', source)
    return prefix + source


def main():
    native = NativeGLES()
    try:
        pairs = shader_pairs()
        for name, vertex, fragment in pairs:
            try:
                native.link(vertex, fragment)
            except AssertionError as error:
                raise AssertionError(f'{name}: {error}') from error
        print(json.dumps({'native_shader_pairs_compiled_and_linked': len(pairs), 'pairs': [p[0] for p in pairs], 'driver': native.driver, 'scope': 'Native GLSL ES compiler/linker check; not browser or visual verification'}, indent=2))
    finally:
        native.close()


if __name__ == '__main__':
    main()
