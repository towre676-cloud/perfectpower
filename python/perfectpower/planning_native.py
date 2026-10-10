"""Optional C++17 exact binary planner, bounded inputs and work budgets."""
import ctypes as C
import hashlib
import json
import shutil
import subprocess
import tempfile
import weakref
import threading
from pathlib import Path
from math import lcm
from .resources import runtime_root
from .divisor_square import WorkLimit

_LIBRARY = None

def available():
    return shutil.which('g++') is not None or _LIBRARY is not None

def library():
    global _LIBRARY
    if _LIBRARY is None:
        compiler=shutil.which('g++')
        if compiler is None: raise WorkLimit('optional native planner requires a C++17 compiler')
        source=runtime_root()/'native/completion_planner.cpp'
        temporary=tempfile.TemporaryDirectory(prefix='perfectpower-planner-')
        output=Path(temporary.name)/'planner.so'
        try:
            subprocess.run([compiler,'-std=c++17','-O3','-fPIC','-shared',str(source),'-o',str(output)],check=True,capture_output=True,timeout=60)
            lib=C.CDLL(str(output))
        except (OSError,subprocess.SubprocessError) as e:
            temporary.cleanup();raise WorkLimit('optional native planner compilation failed') from e
        common=[C.c_int,C.c_int,C.POINTER(C.c_uint64),C.POINTER(C.c_uint64),C.POINTER(C.c_uint64),C.POINTER(C.c_int64)]
        lib.pp_create.argtypes=common+[C.c_uint64,C.c_uint64,C.POINTER(C.c_void_p)];lib.pp_create.restype=C.c_void_p
        lib.pp_create_gray.argtypes=lib.pp_create.argtypes;lib.pp_create_gray.restype=C.c_void_p
        lib.pp_query.argtypes=[C.c_void_p,C.c_int,C.c_uint64];lib.pp_query.restype=C.c_void_p
        lib.pp_optimize.argtypes=common+[C.c_uint64];lib.pp_optimize.restype=C.c_void_p
        lib.pp_recursive.argtypes=common+[C.c_uint64];lib.pp_recursive.restype=C.c_void_p
        lib.pp_destroy.argtypes=[C.c_void_p];lib.pp_destroy.restype=None
        lib.pp_free.argtypes=[C.c_void_p];lib.pp_free.restype=None
        lib._temporary=temporary
        lib._provenance={'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'compiler':subprocess.check_output([compiler,'--version'],text=True).splitlines()[0], 'flags':['-std=c++17','-O3','-fPIC','-shared'],'scope':'tested native execution; no kernel proof of native algorithm'}
        _LIBRARY=lib
    return _LIBRARY

def parameters(planner):
    if planner.kind!='allocation' or planner.machine_model is not None or any(v[2:5]!=(0,1,2) for v in planner.variables):
        raise ValueError('native route requires independent original binary variables')
    n,m=len(planner.variables),len(planner.lower)
    scale=lcm(*(v[1].denominator for v in planner.variables));profit=[int(v[1]*scale) for v in planner.variables]
    if sum(abs(p) for p in profit)>2**60:raise WorkLimit('native exact objective scaling exceeds signed integer budget')
    return scale,(n,m,(C.c_uint64*m)(*planner.lower),(C.c_uint64*m)(*planner.upper),(C.c_uint64*(n*m))(*(x for v in planner.variables for x in v[0])),(C.c_int64*n)(*profit))

def result(lib,pointer):
    if not pointer:raise WorkLimit('native result allocation failed')
    try:r=json.loads(C.string_at(pointer))
    finally:lib.pp_free(pointer)
    if 'error' in r:raise WorkLimit(r['error'])
    for k in ('count','ties','mask'):r[k]=int(r[k])
    return r

class NativeIndex:
    def __init__(self,planner,exhaustive=False):
        self.lib=library();self.scale,args=parameters(planner);self.n=args[0]
        error=C.c_void_p()
        self.handle=(self.lib.pp_create_gray if exhaustive else self.lib.pp_create)(*args,planner.native_records,planner.native_visits,C.byref(error))
        if not self.handle:
            message=C.string_at(error).decode() if error.value else 'native allocation failed'
            if error.value:self.lib.pp_free(error)
            raise WorkLimit(message)
        self._finalizer=weakref.finalize(self,self.lib.pp_destroy,self.handle)
        self.cache={};self.query_visits=0;self.lock=threading.RLock()
    def query(self,prefix):
        with self.lock:
            return self._query(prefix)
    def _query(self,prefix):
        if len(prefix)>self.n or any(type(x) is not int or x not in (0,1) for x in prefix):raise ValueError('binary original-coordinate prefix required')
        key=tuple(prefix)
        if key not in self.cache:
            mask=0
            for x in prefix:mask=2*mask+x
            r=result(self.lib,self.lib.pp_query(self.handle,len(prefix),mask));self.query_visits+=r['visits']
            if len(self.cache)>=8192:self.cache.clear()
            self.cache[key]=r
        return self.cache[key]

def optimize(planner):
    lib=library();scale,args=parameters(planner)
    r=result(lib,lib.pp_optimize(*args,planner.native_visits))
    return r,scale,lib._provenance


def recursive_reference(planner):
    lib=library();scale,args=parameters(planner)
    return result(lib,lib.pp_recursive(*args,planner.native_visits)),scale
