"""Exact algebraic tests; these do not certify Mordell--Weil ranks or Lean builds."""
import itertools
import json
from fractions import Fraction as Q
from math import isqrt, prod
from pathlib import Path


def square_root(q):
    q = Q(q)
    if q < 0:
        return None
    n, d = isqrt(q.numerator), isqrt(q.denominator)
    return Q(n, d) if n*n == q.numerator and d*d == q.denominator else None


def phi(a, b, P):
    if P is None or P[0] == 0:
        return None
    x, y = P
    return (x + a + b/x, y*(1-b/x**2))


def dual(a, b, P):
    R = phi(-2*a, a*a-4*b, P)
    return None if R is None else (R[0]/4, R[1]/8)


def double(a, b, P):
    if P is None or P[1] == 0:
        return None
    x, y = P
    m = (3*x*x+2*a*x+b)/(2*y)
    u = m*m-a-2*x
    return (u, -y+m*(x-u))


def curve_cases():
    rows = []
    # Only assertions about two-torsion and explicit points; no total torsion classification.
    for a, b, expected_t2, expected_c, order4 in [
        (0, 2, 2, 2, None),
        (0, -1, 4, 1, None),
        (1, -2, 4, 1, None),
        (-1, 1, 2, 2, (1, 1)),
        (3, 1, 2, 2, (-1, 1)),
    ]:
        a, b = Q(a), Q(b)
        disc = a*a-4*b
        assert b and disc
        t2 = {None, (Q(0), Q(0))}
        s = square_root(disc)
        if s is not None:
            t2 |= {((-a+s)/2, Q(0)), ((-a-s)/2, Q(0))}
        # Every rational point of order dividing 2 has y=0: the roots above are exhaustive.
        inter = {phi(a,b,P) for P in t2}
        assert inter <= {None, (Q(0), Q(0))}
        assert all(dual(a,b,P) is None for P in inter)
        assert len(t2) == expected_t2
        c = 2 // len(inter)
        assert c == expected_c and c*len(t2) == 4
        assert (s is not None) == ((Q(0),Q(0)) in inter)
        count = 0
        for d in range(1, 9):
            for n in range(-40, 41):
                x = Q(n,d)
                y = square_root(x*(x*x+a*x+b))
                if y is not None:
                    for yy in {y,-y}:
                        P = (x,yy)
                        assert dual(a,b,phi(a,b,P)) == double(a,b,P)
                        count += 1
        if order4:
            P = tuple(map(Q,order4))
            assert P[1]**2 == P[0]*(P[0]**2+a*P[0]+b)
            assert double(a,b,P) == (Q(0),Q(0))
            assert double(a,b,double(a,b,P)) is None
        rows.append(dict(a=str(a),b=str(b),two_torsion=len(t2),
                         dual_kernel_intersection=len(inter),correction=c,
                         correction_times_two_torsion=c*len(t2),
                         rational_point_composition_checks=count,
                         explicit_order_four_point=order4))
    return rows


def finite_cases():
    # Exhaust all homomorphism pairs among these finite abelian groups, checking
    # the kernel identity even when g f is not doubling; then the doubling cases.
    groups = [(), (2,), (3,), (4,), (2,2)]
    def elements(mods):
        return list(itertools.product(*(range(n) for n in mods)))
    def add(x,y,mods):
        return tuple((a+b)%n for a,b,n in zip(x,y,mods))
    def homs(src,dst):
        es, ed = elements(src), elements(dst)
        for images in itertools.product(ed,repeat=len(src)):
            if any(any(n*v % m for v,m in zip(im,dst)) for n,im in zip(src,images)):
                continue
            yield {x:tuple(sum(x[i]*images[i][j] for i in range(len(src)))%dst[j]
                           for j in range(len(dst))) for x in es}
    total = doubling_cases = 0
    examples = []
    for gs in groups:
        G = elements(gs); zg = tuple(0 for _ in gs)
        for hs in groups:
            H = elements(hs); zh = tuple(0 for _ in hs)
            for f in homs(gs,hs):
                for g in homs(hs,gs):
                    rf = set(f.values()); rg = set(g.values())
                    kf = {x for x in G if f[x] == zh}
                    kg = {y for y in H if g[y] == zg}
                    kcomp = {x for x in G if g[f[x]] == zg}
                    c = len(kg)//len(rf & kg)
                    assert c*len(kcomp) == len(kf)*len(kg)
                    rcomp = {g[f[x]] for x in G}
                    assert c*(len(G)//len(rcomp)) == (len(H)//len(rf))*(len(G)//len(rg))
                    total += 1
                    if all(g[f[x]] == add(x,x,gs) for x in G):
                        doubling_cases += 1
                        assert c*len(kcomp) == len(kf)*len(kg)
                        if len(kf)==len(kg)==2:
                            assert c*len(kcomp)==4
                            examples.append(dict(G=gs,H=hs,correction=c,two_torsion=len(kcomp)))
    return dict(homomorphism_pairs=total,doubling_pairs=doubling_cases,
                degree_two_kernel_examples=examples)


if __name__ == '__main__':
    result = dict(status='exact_python_checks_passed',lean_replay='not_run',
                  rank_certified=False,curves=curve_cases(),finite_groups=finite_cases())
    path=Path(__file__).resolve().parents[1]/'receipts/descent_t3/exact_checks.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
