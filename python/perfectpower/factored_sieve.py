"""Prime-power depth tables and finite factored power filters.

No combined CRT table is materialized. A bounded progression wheel supplies
candidates; extra local depth tests reject candidates before root extraction.
Local survival is necessary, never an integer-solution or height theorem.
"""
from fractions import Fraction
from functools import lru_cache
from heapq import merge
from math import gcd,lcm,isqrt
import json
from .residue_cover import integer_polynomial,evaluate,candidate_count
from .core import integer_power_root
from .divisor_square import WorkLimit

DEFAULT_FACTORS=((2,8),(3,4),(11,1),(13,1),(17,1),(19,1),(23,1),(31,1))


def _parameters(degree,prime,exponent):
    if type(degree) is not int or not 2<=degree<=64:raise ValueError('power in [2,64] required')
    if type(prime) is not int or not 2<=prime<=257 or any(prime%q==0 for q in range(2,isqrt(prime)+1)):
        raise ValueError('prime in [2,257] required')
    if type(exponent) is not int or not 1<=exponent<=4096:raise ValueError('depth in [1,4096] required')


def power_residue(value,degree,prime,exponent):
    """Exact d-th-power membership modulo p^a, including zero and nonunits.

    Odd-prime units are cyclic. Dyadic units use their separate sign and
    principal-unit factors; no cyclic odd-prime formula is applied at two.
    """
    _parameters(degree,prime,exponent)
    if type(value) is not int or abs(value).bit_length()>32768:raise ValueError('bounded integer value required')
    modulus=prime**exponent;v=value%modulus
    if v==0:return True
    depth=0
    while v%prime==0:v//=prime;depth+=1
    if depth%degree:return False
    k=exponent-depth
    if prime!=2:
        phi=(prime-1)*prime**(k-1)
        return pow(v,phi//gcd(degree,phi),prime**k)==1
    if degree%2 or k==1:return True
    if k==2:return v%4==1
    two_depth=0;t=degree
    while t%2==0:t//=2;two_depth+=1
    return v%(2**min(k,two_depth+2))==1


def _modvalue(f,x,m):
    value=0
    for c in reversed(f):value=(value*x+c)%m
    return value


@lru_cache(maxsize=8192)
def _depths(f,d,p,a):
    allowed=(0,);modulus=1;levels=[];work=0
    for e in range(1,a+1):
        nxt=modulus*p;work+=len(allowed)*p
        allowed=tuple(sorted(r+t*modulus for r in allowed for t in range(p)
            if power_residue(_modvalue(f,r+t*modulus,nxt),d,p,e)))
        levels.append((nxt,allowed));modulus=nxt
    return tuple(levels),work


def prime_power_table(coefficients,degree,prime,exponent,*,work_limit=200000):
    f=integer_polynomial(coefficients);_parameters(degree,prime,exponent)
    if type(work_limit) is not int or work_limit<1:raise ValueError('positive table budget required')
    q=prime**exponent
    if q>65536:raise WorkLimit('explicit local table modulus exceeds 65536')
    # This bounds the full lifting tree before construction and cache use.
    if sum(prime**e for e in range(1,exponent+1))>work_limit:raise WorkLimit('local depth table exceeds budget')
    levels,work=_depths(tuple(c%q for c in f),degree,prime,exponent)
    return {'prime':prime,'exponent':exponent,'modulus':q,'levels':levels,'allowed':levels[-1][1],
        'tested_lifts':work,'method':'complete residue lifts with valuation/unit membership'}


def verify_prime_power_table(coefficients,degree,table):
    try:
        rebuilt=prime_power_table(coefficients,degree,table['prime'],table['exponent'])
        return json.dumps(rebuilt,sort_keys=True)==json.dumps(table,sort_keys=True)
    except (ValueError,TypeError,KeyError,ArithmeticError):return False


def factored_cover(base,factors=DEFAULT_FACTORS):
    from .residue_cover import verify_cover
    if not isinstance(base,dict) or base.get('schema')=='pp-factored-cover/1' or not verify_cover(base):raise ValueError('ordinary complete base wheel required')
    factors=tuple(tuple(t) for t in factors)
    if not factors or len(factors)>16 or len(set(factors))!=len(factors):raise ValueError('one to sixteen distinct local factors required')
    f=integer_polynomial(base['coefficients']);d=base['degree']
    tables=[prime_power_table(f,d,*t) for t in factors]
    # Sort by retained density, then modulus, for cheap early rejection.
    tables.sort(key=lambda t:(Fraction(len(t['allowed']),t['modulus']),t['modulus']))
    modulus=lcm(base['modulus'],*(t['modulus'] for t in tables))
    return {'schema':'pp-factored-cover/1','coefficients':f,'degree':d,'base':base,'tables':tables,
        'modulus':modulus,'global_obstruction':base['global_obstruction'] or any(not t['allowed'] for t in tables),
        'combined_residue_table_materialized':False,'execution_verified':False,
        'scope':'complete local necessary filters; finite search only in a supplied bounded interval'}


def verify_factored_cover(cover):
    from .residue_cover import verify_cover
    try:
        if cover['schema']!='pp-factored-cover/1' or cover['execution_verified'] is not False or cover['combined_residue_table_materialized'] is not False:return False
        base=cover['base'];tables=cover['tables'];f=integer_polynomial(cover['coefficients']);d=cover['degree']
        if not isinstance(base,dict) or base.get('schema')=='pp-factored-cover/1' or not verify_cover(base):return False
        if integer_polynomial(base['coefficients'])!=f or base['degree']!=d or not 1<=len(tables)<=16:return False
        factors=[(t['prime'],t['exponent']) for t in tables]
        if len(set(factors))!=len(factors) or not all(verify_prime_power_table(f,d,t) for t in tables):return False
        return type(cover['modulus']) is int and cover['modulus']==lcm(base['modulus'],*(t['modulus'] for t in tables)) and type(cover['global_obstruction']) is bool and cover['global_obstruction']==(base['global_obstruction'] or any(not t['allowed'] for t in tables))
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False


def _candidates(cover,lo,hi,filter_limit):
    if type(lo) is not int or type(hi) is not int or hi<lo:raise ValueError('ordered integer interval required')
    if type(filter_limit) is not int or filter_limit<1:raise ValueError('positive filter budget required')
    if cover['global_obstruction']:return [],0
    base=cover['base'];tested=candidate_count(base,lo,hi)
    if tested>filter_limit:raise WorkLimit('base progressions exceed filter budget; no partial search')
    m=base['modulus'];tables=[(t['modulus'],set(t['allowed'])) for t in cover['tables']]
    ranges=[range(lo+(r-lo)%m,hi+1,m) for r in base['allowed']]
    return [x for x in merge(*ranges) if all(x%q in allowed for q,allowed in tables)],tested


def factored_candidate_count(cover,lo,hi,*,filter_limit=2000000):
    if not verify_factored_cover(cover):raise ValueError('invalid factored cover')
    return len(_candidates(cover,lo,hi,filter_limit)[0])


def scan_factored(cover,lo,hi,*,work_limit=100000,filter_limit=2000000):
    if type(work_limit) is not int or work_limit<1:raise ValueError('positive root budget required')
    if not verify_factored_cover(cover):raise ValueError('invalid factored cover')
    candidates,tested=_candidates(cover,lo,hi,filter_limit)
    if len(candidates)>work_limit:raise WorkLimit('surviving roots exceed budget; no partial answer')
    f=integer_polynomial(cover['coefficients']);d=cover['degree'];points=[]
    for x in candidates:
        root=integer_power_root(evaluate(f,x),d)
        if root is not None:points.extend((x,y) for y in sorted({root,-root} if d%2==0 else {root}))
    return {'points':points,'interval':[lo,hi],'interval_size':hi-lo+1,
        'candidates_checked':len(candidates),'sieve_candidates_tested':tested}


def adaptive_cover(base,lo,hi,*,threshold=128):
    if type(threshold) is not int or threshold<1:raise ValueError('positive adaptation threshold required')
    count=candidate_count(base,lo,hi)
    return factored_cover(base) if threshold<=count<=2000000 else base
