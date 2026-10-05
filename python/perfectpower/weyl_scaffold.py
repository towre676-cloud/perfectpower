"""Exact finite monomial scaffold. Group orbits classify; they do not erase fits."""
from fractions import Fraction
from itertools import product
from collections import Counter
from math import factorial


def rational(x):
    if isinstance(x, bool) or isinstance(x, float):
        raise ValueError('use integers, rational strings or Fraction; no floats')
    return Fraction(x)


def chamber(vector):
    return tuple(sorted((abs(rational(x)) for x in vector), reverse=True))


def orbit_size(vector):
    c = Counter(chamber(vector)); n = len(vector); z = c.pop(Fraction(0), 0)
    return 2**(n-z)*factorial(n)//(factorial(z)*prod_factorials(c.values()))


def prod_factorials(values):
    result = 1
    for v in values:
        result *= factorial(v)
    return result


def search(alphabet, rows, targets, *, weights=None, support=None,
           support_penalty=0, denominator_penalty=0, axis_penalties=None,
           candidate_limit=2_000_000):
    """Exhaust all labeled candidates, retain every exact tied optimum.

    Input log values are supplied rational measurements/approximations, never
    a claim that physical logarithms are rational. No orbit quotient is used.
    """
    a = tuple(sorted(set(map(rational, alphabet))))
    x = tuple(tuple(map(rational, row)) for row in rows)
    y = tuple(map(rational, targets))
    if not a or not x or not x[0] or len(x) != len(y):
        raise ValueError('nonempty alphabet, rectangular rows and matching targets required')
    n = len(x[0])
    if any(len(row) != n for row in x):
        raise ValueError('ragged rows')
    if type(candidate_limit) is not int or candidate_limit < 1:
        raise ValueError('positive candidate limit required')
    if len(a)**n > candidate_limit:
        raise ValueError('candidate budget exceeded before enumeration')
    if support is None: support = n
    if type(support) is not int or not 0 <= support <= n:
        raise ValueError('invalid support bound')
    w = tuple(map(rational, weights)) if weights is not None else (Fraction(1,len(x)),)*len(x)
    p = tuple(map(rational, axis_penalties)) if axis_penalties is not None else (Fraction(0),)*n
    sp, dp = rational(support_penalty), rational(denominator_penalty)
    if len(w)!=len(x) or any(v<0 for v in w) or sum(w)<=0 or len(p)!=n or any(v<0 for v in p) or sp<0 or dp<0:
        raise ValueError('invalid weights or penalties')
    best = None; winners = []; tested = 0; classes = set()
    for r in product(a, repeat=n):
        active = sum(v != 0 for v in r)
        if active > support: continue
        tested += 1; classes.add(chamber(r))
        score = sum(wj*(yj-sum(v*t for v,t in zip(r,row)))**2 for wj,yj,row in zip(w,y,x))
        score += sp*active + dp*sum(v.denominator for v in r if v) + sum(pi for pi,v in zip(p,r) if v)
        if best is None or score < best:
            best = score; winners = [r]
        elif score == best: winners.append(r)
    return {'scope':'complete finite supplied-rational objective', 'score':None if best is None else str(best),
            'tested':tested,'orbit_classes':len(classes),
            'winners':[[str(v) for v in r] for r in winners],
            'winner_orbit_sizes':[orbit_size(r) for r in winners]}


def symmetry_defect(gram, linear):
    """Full signed-permutation invariance of r^T G r - 2 c^T r.

    For symmetric G it holds iff G is scalar identity and c is zero.
    Priors/constraints require separate invariance checks.
    """
    g=tuple(tuple(map(rational,row)) for row in gram); c=tuple(map(rational,linear)); n=len(c)
    if not n or len(g)!=n or any(len(row)!=n for row in g): raise ValueError('shape mismatch')
    if any(g[i][j]!=g[j][i] for i in range(n) for j in range(n)): raise ValueError('symmetric Gram required')
    return {'invariant': all(v==0 for v in c) and all(g[i][j]==(g[0][0] if i==j else 0) for i in range(n) for j in range(n))}
