"""Exact indexed, counted and residue-filtered square-triangular size queries.

Uses the complete orbit of SquareTriangular.triIdx_iff, with integer powering
and monotone boundary search. Python evaluation is not a Lean certificate.
"""
from math import lcm
from .recurrence import filter_count,CycleLimit


def _natural(value,name):
    if type(value) is not int or value<0:raise ValueError(f'{name} must be a nonnegative integer')


def _times(a,b):
    return a[0]*b[0]+8*a[1]*b[1],a[0]*b[1]+a[1]*b[0]


def orbit(index):
    """(X_j,Y_j)=(3+sqrt(8))^j, by binary exact integer powering."""
    _natural(index,'index');out=(1,0);base=(3,1)
    while index:
        if index&1:out=_times(out,base)
        index//=2
        if index:base=_times(base,base)
    return out


def point(index):
    x,y=orbit(index);n=(x-1)//2
    if x%2!=1 or n*(n+1)!=2*y*y:raise AssertionError('orbit coordinate identity failed')
    return n,y


def last_index(bound):
    """Largest j≥0 with triangular index n_j≤bound, no logarithm rounding."""
    _natural(bound,'bound')
    lo,hi=0,1;calls=0
    while point(hi)[0]<=bound:lo,hi=hi,2*hi;calls+=1
    calls+=1
    while hi-lo>1:
        mid=(lo+hi)//2;calls+=1
        if point(mid)[0]<=bound:lo=mid
        else:hi=mid
    return lo,calls


def residue_schedule(filters=(),*,state_limit=100_000):
    """Full-state modular cycle; filters are ('index'|'root', modulus, residue).

    To recover n=(X-1)/2 modulo m, X is tracked modulo 2m, preserving
    the extra factor of two. The invertible unit gives no preperiod.
    """
    filters=tuple(tuple(f) for f in filters);modulus=1
    if type(state_limit) is not int or state_limit<1:raise ValueError('positive state budget required')
    for f in filters:
        if len(f)!=3 or f[0] not in ('index','root') or type(f[1]) is not int or f[1]<1 or type(f[2]) is not int:
            raise ValueError('exact coordinate, positive modulus and integer residue required')
        modulus=lcm(modulus,f[1])
    m=2*modulus;state=(1%m,0);start=state;hits=[];states=[]
    while True:
        if len(states)>=state_limit:raise CycleLimit('square-triangular modular state budget exceeded')
        j=len(states);states.append(state);n=(state[0]-1)//2;y=state[1]
        if all((n if coord=='index' else y)%d==r%d for coord,d,r in filters):hits.append(j)
        state=((3*state[0]+8*state[1])%m,(state[0]+3*state[1])%m)
        if state==start:break
    return {'period':len(states),'preperiod':0,'prefix_hits':[],'cycle_hits':hits,
            'state_modulus':m,'filters':filters,'initial_state':start,'execution_verified':False}


def query(bound,filters=(),*,state_limit=100_000):
    _natural(bound,'bound');j,calls=last_index(bound);schedule=residue_schedule(filters,state_limit=state_limit)
    count=filter_count(schedule,j+1)-int(0 in schedule['cycle_hits'])
    return {'bound':bound,'unfiltered_count':j,'filtered_count':count,'last_orbit_index':j,
            'last_unfiltered_point':point(j) if j else None,'first_point_above_bound':point(j+1),
            'boundary_power_evaluations':calls,'schedule':schedule,'complete':True,
            'theorem':'PerfectPower.SquareTriangular.triIdx_iff','execution_verified':False,
            'scope':'positive triangular indices n<=bound; nonnegative square roots'}


def select(rank,filters=(),*,state_limit=100_000):
    """Zero-based selection among positive solutions satisfying the residues."""
    _natural(rank,'rank');s=residue_schedule(filters,state_limit=state_limit)
    positives=sorted(j if j else s['period'] for j in s['cycle_hits'])
    if not positives:raise ValueError('no positive solution satisfies these residue filters')
    index=(rank//len(positives))*s['period']+positives[rank%len(positives)]
    return {'rank':rank,'orbit_index':index,'point':point(index),'schedule':s,'execution_verified':False}
