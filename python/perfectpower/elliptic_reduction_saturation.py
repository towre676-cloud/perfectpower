"""Exact good-reduction exclusions for prime divisibility of a full-rank lattice.

An empty intersection of surviving projective coefficient lines proves that
the supplied points are independent in E(Q)/ell E(Q). Full rational rank and
a global bound on saturation primes are separate inputs, never inferred by
this finite computation. Failure to exclude a line remains inconclusive.
"""
from functools import lru_cache
from itertools import product
from .elliptic_arithmetic import EllipticCurve,primes


def add(p,a,b):
    if a is None:return b
    if b is None:return a
    x,y=a;u,v=b
    if x==u and (y+v)%p==0:return None
    m=((3*x*x)*pow(2*y,-1,p) if a==b else (v-y)*pow(u-x,-1,p))%p
    xx=(m*m-x-u)%p
    return xx,(m*(x-xx)-y)%p


def multiply(p,point,n):
    out=None
    while n:
        if n&1:out=add(p,out,point)
        point=add(p,point,point);n//=2
    return out


@lru_cache(maxsize=2048)
def finite_group(k,p):
    roots={}
    for y in range(p):roots.setdefault(y*y%p,[]).append(y)
    return (None,)+tuple((x,y) for x in range(p) for y in roots.get((x**3+k)%p,[]))


@lru_cache(maxsize=4096)
def multiple_image(k,p,ell):
    return frozenset(multiply(p,point,ell) for point in finite_group(k,p))


def reduce_point(point,p):
    if point is None:return None
    x,y=point
    if x.denominator%p==0:return None
    if y.denominator%p==0:raise ArithmeticError('inconsistent good-reduction coordinates')
    return (x.numerator*pow(x.denominator,-1,p)%p,
            y.numerator*pow(y.denominator,-1,p)%p)


def coefficient_lines(ell,rank):
    return [v for v in product(range(ell),repeat=rank)
            if any(v) and next(c for c in v if c)==1]


def reduction_saturation(k,points,ell,auxiliary_bound=2000):
    if type(k) is not int or not k or abs(k)>10**6:raise ValueError('bounded Mordell coefficient required')
    if type(ell) is not int or ell not in primes(97):raise ValueError('prime at most 97 required')
    if not isinstance(points,list) or not 1<=len(points)<=2:raise ValueError('one or two rational points required')
    if type(auxiliary_bound) is not int or not 5<=auxiliary_bound<=2000:raise ValueError('bounded auxiliary primes required')
    E=EllipticCurve([0,k]);basis=[E.checked(p) for p in points]
    remaining=coefficient_lines(ell,len(points));steps=[]
    for p in primes(auxiliary_bound):
        if p==ell or (6*k)%p==0:continue
        group=finite_group(k%p,p)
        if len(group)%ell:continue
        image=multiple_image(k%p,p,ell);reduced=[reduce_point(P,p) for P in basis]
        keep=[]
        for cs in remaining:
            total=None
            for c,P in zip(cs,reduced):total=add(p,total,multiply(p,P,c))
            if total in image:keep.append(cs)
        if len(keep)<len(remaining):
            steps.append(dict(auxiliary_prime=p,group_order=len(group),
                              surviving_before=len(remaining),surviving_after=len(keep)))
        remaining=keep
        if not remaining:break
    return dict(schema='pp-elliptic-reduction-saturation/1',k=k,points=points,prime=ell,
        auxiliary_bound=auxiliary_bound,reductions=steps,
        surviving_lines=[list(v) for v in remaining],
        independent_mod_prime=not remaining,
        scope='exact exclusion of rational prime divisibility for every nonzero projective coefficient line; full rank and global prime bound are separate')


def replay_reduction_saturation(packet):
    try:
        computed=reduction_saturation(packet['k'],packet['points'],packet['prime'],packet['auxiliary_bound'])
        return computed==packet and packet['independent_mod_prime'] is True
    except (ValueError,KeyError,TypeError,ArithmeticError):return False
