"""Exact, unweighted DIMACS CNF counting and original-variable queries.

Component caches use full normalized clause keys, never probabilistic identities.
Native execution is tested; no new Lean/kernel certification is asserted.
"""
from dataclasses import dataclass
from pathlib import Path
from random import Random, SystemRandom
from threading import Lock
import ctypes
import hashlib
import json
import os
import subprocess
import tempfile
import time
from .resources import runtime_root
from .divisor_square import WorkLimit

MAX_VARIABLES=200_000
MAX_CLAUSES=2_000_000
MAX_BYTES=64*1024*1024

@dataclass(frozen=True)
class CNF:
    variables: int
    clauses: tuple
    def __post_init__(self):
        if type(self.variables) is not int or not 0<=self.variables<=MAX_VARIABLES:
            raise ValueError('CNF variable count outside supported range')
        normalized=[]
        if len(self.clauses)>MAX_CLAUSES:raise WorkLimit('CNF clause limit')
        for clause in self.clauses:
            literals=set()
            for x in clause:
                if type(x) is not int or x==0 or abs(x)>self.variables:raise ValueError('literal outside declared variables')
                literals.add(x)
            if not any(-x in literals for x in literals):normalized.append(tuple(sorted(literals)))
        object.__setattr__(self,'clauses',tuple(sorted(set(normalized))))
    @classmethod
    def parse(cls,text):
        if not isinstance(text,str):raise TypeError('DIMACS text required')
        if len(text.encode('utf8'))>MAX_BYTES:raise WorkLimit('CNF byte limit')
        header=None;clauses=[];current=[];terminated=False
        for line in text.splitlines():
            tokens=line.split()
            if not tokens:continue
            if tokens[0]=='c':
                if tokens[1:3] in (['p','weight'],['p','show']) or tokens[1:2]==['weights']:
                    raise ValueError('weighted/projected semantics unsupported; unweighted CNF required')
                continue
            if tokens[0]=='p':
                if header is not None or current or clauses or len(tokens)!=4 or tokens[1]!='cnf':raise ValueError('one DIMACS p cnf header required')
                try:n,m=map(int,tokens[2:])
                except ValueError as e:raise ValueError('integer DIMACS dimensions required') from e
                if n<0 or m<0:raise ValueError('nonnegative dimensions required')
                if n>MAX_VARIABLES or m>MAX_CLAUSES:raise WorkLimit('declared CNF dimension limit')
                header=(n,m);continue
            if tokens==['%']:
                if current or header is None or len(clauses)!=header[1]:raise ValueError('premature DIMACS terminator')
                terminated=True;continue
            if terminated:raise ValueError('input after DIMACS terminator')
            if header is None:raise ValueError('DIMACS header required before literals')
            for token in tokens:
                try:x=int(token)
                except ValueError as e:raise ValueError('integer DIMACS literal required') from e
                if x==0:
                    clauses.append(tuple(current));current=[]
                    if len(clauses)>header[1]:raise ValueError('too many DIMACS clauses')
                else:
                    if abs(x)>header[0]:raise ValueError('literal outside declared variables')
                    current.append(x)
        if header is None or current or len(clauses)!=header[1]:raise ValueError('terminated clauses matching header required')
        return cls(header[0],tuple(clauses))
    @classmethod
    def read(cls,path):
        p=Path(path)
        if p.stat().st_size>MAX_BYTES:raise WorkLimit('CNF byte limit')
        return cls.parse(p.read_text(encoding='utf8'))
    def dimacs(self,assumptions=()):
        locks=_assumptions(assumptions,self.variables)
        clauses=self.clauses+tuple((x,) for x in locks)
        return f'p cnf {self.variables} {len(clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in clauses)
    def accepts(self,point):
        _point(point,self.variables)
        return all(any(point[abs(x)-1]==int(x>0) for x in c) for c in self.clauses)

def _assumptions(literals,n):
    if isinstance(literals,(str,bytes)):raise ValueError('assumption literals required')
    out=tuple(literals)
    if any(type(x) is not int or not 1<=abs(x)<=n for x in out):raise ValueError('assumption literal outside declared variables')
    return out

def _point(point,n):
    if not isinstance(point,(tuple,list)) or len(point)!=n or any(type(x) is not int or x not in (0,1) for x in point):raise ValueError('original binary point required')

def exact_decimal(text):
    """Decode arbitrarily long nonnegative decimal without changing global limits."""
    if not isinstance(text,str) or not text or not text.isascii() or not text.isdigit():raise ValueError('nonnegative decimal count required')
    value=0
    for start in range(0,len(text),9):
        chunk=text[start:start+9];value=value*10**len(chunk)+int(chunk)
    return value

_library=None
_compile_lock=Lock()
def native_library():
    global _library
    with _compile_lock:
        if _library is not None:return _library
        source=runtime_root()/'native/model_counting/counter.cpp'
        digest=hashlib.sha256(source.read_bytes()).hexdigest()
        cache=Path(tempfile.gettempdir())/'perfectpower-model-counting';cache.mkdir(exist_ok=True)
        target=cache/(digest+'.so')
        if not target.exists():
            fd,path=tempfile.mkstemp(suffix='.so',dir=cache);os.close(fd)
            cmd=[os.environ.get('CXX','g++'),'-std=c++17','-O3','-fPIC','-shared',str(source),'-o',path]
            include=os.environ.get('PP_CNF_BOOST_INCLUDE')
            if include:cmd.extend(['-I',include])
            try:
                result=subprocess.run(cmd,capture_output=True,text=True,timeout=120)
                if result.returncode:raise WorkLimit('optional CNF native backend requires g++ and Boost headers: '+result.stderr[-2000:])
                os.replace(path,target)
            finally:
                if os.path.exists(path):os.unlink(path)
        lib=ctypes.CDLL(str(target))
        lib.pp_cnf_new.argtypes=[ctypes.c_char_p,ctypes.c_size_t];lib.pp_cnf_new.restype=ctypes.c_void_p
        lib.pp_cnf_delete.argtypes=[ctypes.c_void_p];lib.pp_cnf_delete.restype=None
        lib.pp_cnf_count.argtypes=[ctypes.c_void_p,ctypes.POINTER(ctypes.c_int),ctypes.c_uint,ctypes.c_uint];lib.pp_cnf_count.restype=ctypes.c_char_p
        _library=lib;return lib

class CNFCounter:
    def __init__(self,formula,*,cache_bytes=128*1024*1024,timeout=120):
        if not isinstance(formula,CNF):raise TypeError('CNF formula required')
        if type(cache_bytes) is not int or not 0<=cache_bytes<=1024**3:raise ValueError('cache bytes 0..1GiB required')
        if isinstance(timeout,bool) or not isinstance(timeout,(int,float)) or not 0<timeout<=3600:raise ValueError('timeout in (0,3600] required')
        self.formula=formula;self.timeout=timeout;self._lock=Lock();self._lib=native_library()
        wire=f'{formula.variables} {len(formula.clauses)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in formula.clauses)
        self._handle=self._lib.pp_cnf_new(wire.encode('ascii'),cache_bytes)
        if not self._handle:raise WorkLimit('native formula allocation failed')
        self.last=None
    def close(self):
        with self._lock:
            if self._handle:self._lib.pp_cnf_delete(self._handle);self._handle=None
    def __enter__(self):return self
    def __exit__(self,*args):self.close()
    def __del__(self):
        if getattr(self,'_handle',None):self.close()
    def result(self,assumptions=(),*,timeout=None):
        locks=_assumptions(assumptions,self.formula.variables)
        limit=self.timeout if timeout is None else timeout
        if isinstance(limit,bool) or not isinstance(limit,(int,float)) or not 0<limit<=3600:raise ValueError('timeout in (0,3600] required')
        array=(ctypes.c_int*len(locks))(*locks)
        with self._lock:
            if not self._handle:raise ValueError('closed CNF counter')
            answer=json.loads(self._lib.pp_cnf_count(self._handle,array,len(locks),max(1,int(limit*1000))).decode())
            self.last=answer.copy();return answer
    def count(self,assumptions=(),*,timeout=None):
        answer=self.result(assumptions,timeout=timeout)
        if answer['status']=='WORK_LIMIT':raise WorkLimit(answer['reason'])
        if answer['status']!='EXACT':raise RuntimeError(answer.get('reason','native counting error'))
        return exact_decimal(answer['count'])
    def _deadline(self):return time.monotonic()+self.timeout
    def _remaining(self,deadline):
        remaining=deadline-time.monotonic()
        if remaining<=0:raise WorkLimit('complete original-variable query time limit')
        return min(remaining,3600)
    def select(self,rank,assumptions=()):
        if type(rank) is not int or rank<0:raise ValueError('nonnegative integer rank required')
        locks=_assumptions(assumptions,self.formula.variables);deadline=self._deadline()
        return self._select(rank,locks,deadline)
    def _select(self,rank,locks,deadline,total=None):
        total=self.count(locks,timeout=self._remaining(deadline)) if total is None else total
        if rank>=total:raise ValueError('rank outside conditional model population')
        fixed={abs(x):int(x>0) for x in locks};point=[];prefix=list(locks)
        for v in range(1,self.formula.variables+1):
            if v in fixed:point.append(fixed[v]);continue
            left=self.count(prefix+[-v],timeout=self._remaining(deadline))
            bit=int(rank>=left)
            if bit:rank-=left
            point.append(bit);prefix.append(v if bit else -v)
        return point
    def rank(self,point,assumptions=()):
        _point(point,self.formula.variables);locks=_assumptions(assumptions,self.formula.variables)
        if not self.formula.accepts(point) or any(point[abs(x)-1]!=int(x>0) for x in locks):raise ValueError('point is not a conditional model')
        deadline=self._deadline();prefix=list(locks);fixed={abs(x) for x in locks};rank=0
        for v,bit in enumerate(point,1):
            if v in fixed:continue
            if bit:rank+=self.count(prefix+[-v],timeout=self._remaining(deadline))
            prefix.append(v if bit else -v)
        return rank
    def sample(self,assumptions=(),*,seed=None):
        if seed is not None and type(seed) is not int:raise ValueError('integer seed required')
        locks=_assumptions(assumptions,self.formula.variables);deadline=self._deadline()
        count=self.count(locks,timeout=self._remaining(deadline))
        if count==0:raise ValueError('cannot sample an empty model population')
        return self._select((SystemRandom() if seed is None else Random(seed)).randrange(count),locks,deadline,count)

def add_commands(sub):
    p=sub.add_parser('model-count',help='exact unweighted DIMACS CNF count');p.add_argument('file');p.add_argument('--assume',type=int,action='append',default=[]);p.add_argument('--timeout',type=float,default=120);p.add_argument('--cache-mib',type=int,default=128)

def cli(args):
    if args.command!='model-count':return False
    with CNFCounter(CNF.read(args.file),cache_bytes=args.cache_mib*1024**2,timeout=args.timeout) as counter:
        print(json.dumps(counter.result(args.assume)))
    return True
