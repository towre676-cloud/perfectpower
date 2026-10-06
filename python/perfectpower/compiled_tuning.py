"""Real compiled integer matrix workload, interleaved with conventional C."""
from pathlib import Path
from tempfile import TemporaryDirectory
from hashlib import sha256
import ctypes
import subprocess
import shutil
from array import array
from .populations import ExactPopulation
from .configuration_tuning import tune


def compatible_tiles(max_parameter=12,max_tile_bytes=262144):
    if type(max_parameter) is not int or not 1<=max_parameter<=64 or type(max_tile_bytes) is not int or not 1<=max_tile_bytes<=2**30:
        raise ValueError('bounded tile parameter and byte capacity required')
    predicate={'op':'and','args':[{'poly':[-1,1],'relation':'>='},{'poly':[-max_parameter,1],'relation':'<='},
        {'poly':[-max_tile_bytes,0,0,0,0,8],'relation':'<='}]}
    return ExactPopulation(dict(kind='domain',predicate=predicate,fields={'row_block':[0,0,0,1],
        'column_block':[0,0,1],'tile_bytes':[0,0,0,0,0,8]}))


class CompiledMatmul:
    def __init__(self,left,right,compiler=None):
        n=len(left)
        if not 1<=n<=512 or len(right)!=n or any(len(r)!=n for r in list(left)+list(right)):
            raise ValueError('matching square matrices of order 1 through 512 required')
        flat_a=[v for row in left for v in row];flat_b=[v for row in right for v in row]
        if any(type(v) is not int or not 0<=v<=65535 for v in flat_a+flat_b):raise ValueError('16-bit unsigned input values required')
        executable=compiler or shutil.which('cc')
        if executable is None:raise ValueError('C compiler required for this workload')
        self.temporary=TemporaryDirectory(prefix='perfectpower-kernel-');self.n=n
        source=Path(__file__).resolve().parents[2]/'native'/'compatible_matmul.c'
        output=Path(self.temporary.name)/'matmul.so';flags=['-std=c99','-O3','-fPIC','-shared']
        try:subprocess.run([executable,*flags,str(source),'-o',str(output)],check=True,capture_output=True,text=True)
        except BaseException:self.temporary.cleanup();raise
        self.library=ctypes.CDLL(str(output));self.a=(ctypes.c_uint32*(n*n))(*flat_a);self.b=(ctypes.c_uint32*(n*n))(*flat_b)
        self.output=(ctypes.c_uint64*(n*n))()
        common=[ctypes.c_size_t,ctypes.POINTER(ctypes.c_uint32),ctypes.POINTER(ctypes.c_uint32),ctypes.POINTER(ctypes.c_uint64)]
        self.library.pp_naive.argtypes=common;self.library.pp_naive.restype=None
        self.library.pp_untiled.argtypes=common;self.library.pp_untiled.restype=None
        self.library.pp_tiled.argtypes=common+[ctypes.c_size_t,ctypes.c_size_t];self.library.pp_tiled.restype=None
        self.provenance=dict(compiler=subprocess.check_output([executable,'--version'],text=True).splitlines()[0],
            flags=flags,source_sha256=sha256(source.read_bytes()).hexdigest(),element_bits=64,
            overflow_bound=n*65535**2,scope='bounded exact integer C kernels, including ctypes call and result-byte transport in measured times')

    def __enter__(self):return self
    def __exit__(self,*args):self.temporary.cleanup()

    def conventional(self):
        self.library.pp_naive(self.n,self.a,self.b,self.output)
        return bytes(self.output)

    def untiled(self):
        self.library.pp_untiled(self.n,self.a,self.b,self.output)
        return bytes(self.output)

    def tiled(self,values):
        rows,columns=values['row_block'],values['column_block']
        if any(type(x) is not int or not 1<=x<=2**20 for x in (rows,columns)):
            raise ValueError('bounded positive tile dimensions required')
        self.library.pp_tiled(self.n,self.a,self.b,self.output,rows,columns)
        return bytes(self.output)


def benchmark(n=192,repeats=7,seed=622,max_tile_bytes=262144):
    if type(n) is not int or not 1<=n<=512:raise ValueError('matrix order 1 through 512 required')
    left=[[(i*17+k*5)%251 for k in range(n)] for i in range(n)]
    right=[[(k*7+j*3)%241 for j in range(n)] for k in range(n)]
    columns=list(zip(*right))
    expected=array('Q',(sum(a*b for a,b in zip(row,col)) for row in left for col in columns)).tobytes()
    population=compatible_tiles(max_tile_bytes=max_tile_bytes)
    with CompiledMatmul(left,right) as kernel:
        result=tune(population,kernel.tiled,expected,repeats=repeats,warmups=2,seed=seed,comparison=kernel.conventional,controls={'cache_friendly_untiled':kernel.untiled})
        result.update(compilation=kernel.provenance,workload=dict(order=n,operations=2*n**3,
            output_sha256=sha256(expected).hexdigest(),tile_byte_budget=max_tile_bytes,
            tile_semantics='conservative full rectangular output-tile footprint; boundary tiles are clipped'),
            reference='independent Python dot products; every full byte output checked',
            comparison_scope='conventional and tiled C compiled together with identical flags, interleaved on this host')
    return result
