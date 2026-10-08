"""Bounded exact reduction of Mordell covering models, with retained transports.

Unimodular coefficient descent and local integral scaling moves are proposals.
No global minimality, orbit classification or exhaustive rational-point claim
is attached to the result. Invariants are fingerprints, never equivalence proofs.
"""
from fractions import Fraction as Q
from math import gcd, isqrt
from functools import reduce
from .binary_invariants import form, binary_substitute, quartic_invariants
from .mordell_cover_charts import chart_cover, projective_cover_lift
from .elliptic_two_descent import quartic_map

IDENTITY = [[1,0],[0,1]]


def _score(f):
    return (abs(quartic_invariants(f)['discriminant']), max(map(abs,f)), sum(map(abs,f)))


def _compose(a,b):
    return [[sum(a[i][h]*b[h][j] for h in range(2)) for j in range(2)] for i in range(2)]


def _square_part(n):
    # Bounded factor extraction; an unfactored large content is simply retained.
    n = abs(n); answer = 1; p = 2
    while p*p <= n and p <= 1000:
        count = 0
        while n % p == 0: n//=p; count+=1
        answer *= p**(count//2)
        p += 1 if p == 2 else 2
    root=isqrt(n)
    if root*root==n:answer*=root
    return answer


def _moves(f, primes):
    # Small exact GL2(Z) neighborhood, augmented by coefficient-centering shears.
    moves = [(IDENTITY,1)]
    for a in range(-2,3):
        for b in range(-2,3):
            for c in range(-2,3):
                for d in range(-2,3):
                    if a*d-b*c in (-1,1): moves.append(([[a,b],[c,d]],1))
    for numerator,denominator in ((-f[3],4*f[4]),(-f[1],4*f[0])):
        if denominator:
            center = numerator//denominator
            for shift in range(int(center)-2,int(center)+3):
                if abs(shift) <= 10000:
                    moves.extend([([[1,shift],[0,1]],1),([[1,0],[shift,1]],1)])
    # Removing square content is a Q-isomorphism of the weighted cover.
    content = reduce(gcd,(int(v) for v in f),0)
    square = _square_part(content)
    if square > 1: moves.append((IDENTITY,square))
    # Exact p-adic chart proposals. Integral acceptance tests every coefficient.
    for p in primes:
        for r in range(p):
            for e in (p,p*p):
                moves.extend([([[p,r],[0,1]],e),([[r,p],[1,0]],e)])
    return moves


def reduce_cover(k, cover, *, max_steps=8, primes=(2,3,5,7)):
    """Strictly decrease (|disc|, coefficient infinity norm, coefficient 1-norm)."""
    if type(max_steps) is not int or not 0 <= max_steps <= 32:
        raise ValueError('at most 32 reduction steps')
    if any(type(p) is not int or p not in (2,3,5,7,11,13) for p in primes):
        raise ValueError('supported small local primes required')
    quartic_map(k,cover)
    f = form(cover['quartic'],4)
    if any(v.denominator != 1 for v in f): raise ValueError('integral cover required')
    if not quartic_invariants(f)['discriminant']: raise ValueError('smooth binary quartic required')
    start = f; matrix = IDENTITY; scale = 1; steps=[]
    for _ in range(max_steps):
        best=None; seen=set();old_score=_score(f)
        for M,e in _moves(f,primes):
            g=tuple(v/e**2 for v in binary_substitute(f,4,M))
            if g in seen: continue
            seen.add(g)
            if any(v.denominator != 1 for v in g): continue
            score=_score(g)
            if score >= old_score: continue
            total=_compose(matrix,M); total_scale=scale*e
            if max(abs(v) for row in total for v in row)>1000000 or total_scale>1000000: continue
            candidate=(score,tuple(v for row in total for v in row),total_scale)
            if best is None or candidate < best[0]:best=(candidate,M,e,g,total,total_scale)
        if best is None: break
        _,M,e,g,total,total_scale=best
        steps.append(dict(matrix=M,ordinate_scale=e,before=[str(v) for v in f],after=[str(v) for v in g]))
        f,matrix,scale=g,total,total_scale
    chart=chart_cover(k,cover,matrix,scale)
    if form(chart['cover']['quartic'],4) != f: raise ArithmeticError('composed reduction disagrees')
    before,after=quartic_invariants(start),quartic_invariants(f)
    det=chart['determinant']
    for key,weight in [('I',4),('J',6),('discriminant',12)]:
        if after[key] != before[key]*Q(det,scale)**weight:
            raise ArithmeticError('relative invariant transformation failed')
    return dict(schema='pp-quartic-cover-reduction/1',k=k,chart=chart,steps=steps,
                before_invariants={key:str(before[key]) for key in ('I','J','discriminant')},
                after_invariants={key:str(after[key]) for key in ('I','J','discriminant')},
                score_before=[str(v) for v in _score(start)],score_after=[str(v) for v in _score(f)],
                max_steps=max_steps,local_primes=list(primes),global_minimality=False)


def reduced_projective_lift(reduction, coordinates):
    """Transport finite and infinite weighted points through the combined chart."""
    chart=reduction['chart'];k=chart['k']
    target=projective_cover_lift(k,chart['cover'],coordinates)
    u,v,w=coordinates;(a,b),(c,d)=chart['matrix'];e=chart['ordinate_scale']
    U,V,W=a*u+b*v,c*u+d*v,e*w;g=gcd(U,V)
    if not g or W%(g*g):raise ValueError('invalid primitive source normalization')
    U,V,W=U//g,V//g,W//(g*g)
    if V<0 or (V==0 and U<0):U,V=-U,-V
    source=projective_cover_lift(k,chart['source_cover'],[U,V,W])
    if source['mordell_point']!=target['mordell_point']:raise ArithmeticError('source/target lift mismatch')
    return dict(reduced_coordinates=list(coordinates),**source)


def projective_residue_mask(values, modulus):
    """Necessary square condition, including primitive residues at infinity."""
    if type(modulus) is not int or not 2 <= modulus <= 64:raise ValueError('modulus from 2 through 64')
    f=form(values,4)
    if any(v.denominator!=1 for v in f):raise ValueError('integral binary quartic required')
    f=tuple(map(int,f));squares={i*i%modulus for i in range(modulus)}
    return [(u,v) for u in range(modulus) for v in range(modulus)
            if gcd(gcd(u,v),modulus)==1 and
            sum(a*pow(u,i,modulus)*pow(v,4-i,modulus) for i,a in enumerate(f))%modulus in squares]


def search_reduced_box(reduction, *, height=1000, moduli=(16,9,5,7)):
    """Complete exact enumeration of the stated projective height box only."""
    if type(height) is not int or not 1 <= height <= 10000:raise ValueError('height from 1 through 10000')
    f=tuple(map(int,form(reduction['chart']['cover']['quartic'],4)))
    masks=[(m,set(projective_residue_mask(f,m))) for m in moduli]
    tested=0;rejected=0;points=[]
    for v in range(height+1):
        for u in ([1] if v==0 else range(-height,height+1)):
            if gcd(u,v)!=1:continue
            if any((u%m,v%m) not in mask for m,mask in masks):rejected+=1;continue
            tested+=1;value=sum(a*u**i*v**(4-i) for i,a in enumerate(f))
            if value<=0:continue
            w=isqrt(value)
            if w*w==value:
                for sign in (1,-1):points.append(reduced_projective_lift(reduction,[u,v,sign*w]))
    return dict(schema='pp-reduced-cover-box/1',height=height,moduli=list(moduli),
                square_tests=tested,residue_rejections=rejected,lifts=points,
                exceptional_zero_ordinates_excluded=True,global_empty_proof=False,
                integral_point_completeness=False)
