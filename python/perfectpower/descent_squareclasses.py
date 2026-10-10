"""Complete squareclass candidates and finite exclusions for rational 2-torsion curves.

E: y^2=x(x^2+a*x+b), integer a,b, b*(a^2-4*b) != 0. Covers are
w^2=d*u^4+a*u^2*v^2+(b/d)*v^4 for signed squarefree divisors d of b.
Finite survivors are unresolved, never called Selmer classes or rational points.
"""
from fractions import Fraction as Q
from math import gcd, isqrt
from .divisor_square import Budget, WorkLimit
from .local_quartic import _prime
from .psg_polynomial import rational


def curve(a, b):
    if type(a) is not int or type(b) is not int or not b or a*a == 4*b:
        raise ValueError('nonsingular integral rational-2-torsion model required')
    if max(abs(a).bit_length(), abs(b).bit_length()) > 512:
        raise WorkLimit('curve coefficient exceeds 512 bits')
    return a, b


def _factor(n, budget):
    factors = []
    p = 2
    while p*p <= n:
        budget.spend()
        if n % p == 0:
            e = 0
            while n % p == 0:
                budget.spend(); n //= p; e += 1
            factors.append((p, e))
        p = 3 if p == 2 else p+2
    if n > 1:
        factors.append((n, 1))
    return factors


def squareclasses(a, b, *, work_limit=100_000):
    curve(a, b)
    budget = Budget(work_limit)
    factors = _factor(abs(b), budget)
    if len(factors) > 16:
        raise WorkLimit('squareclass dimension exceeds 16')
    values = [1]
    for p, _ in factors:
        for _ in values:
            budget.spend()
        values += [d*p for d in values]
    return sorted(values+[-d for d in values])


def _cover(a, b, d):
    curve(a, b)
    if type(d) is not int or not d or b % d:
        raise ValueError('nonzero signed divisor of b required')
    # Caller candidate enumeration ensures squarefreeness; public maps check it.
    return d, a, b//d


def real_obstructed(a, b, d):
    d, a, c = _cover(a, b, d)
    # q(s)=d*s^2+a*s+c for s>=0. Infinity has value d.
    return d < 0 and c < 0 and (a <= 0 or a*a < 4*d*c)


def local_cover(a, b, d, prime, depth=1, *, work_limit=100_000):
    """Complete primitive projective chart residues at one finite modulus.

    v=1 with arbitrary u, plus u=1 with v divisible by p. Unit scaling
    preserves quartic-square membership and these charts exhaust primitive pairs.
    """
    d, a, c = _cover(a, b, d)
    if type(prime) is not int or not 2 <= prime <= 257 or not _prime(prime):
        raise ValueError('certified prime <=257 required')
    if type(depth) is not int or not 1 <= depth <= 16:
        raise ValueError('depth in 1..16 required')
    m = prime**depth
    if type(work_limit) is not int or work_limit < 1 or 2*m+m//prime > work_limit:
        raise WorkLimit('local chart construction exceeds work budget')
    squares = {w*w % m for w in range(m)}
    first = [u for u in range(m) if (d*u**4+a*u*u+c) % m in squares]
    second = [v for v in range(0, m, prime) if (d+a*v*v+c*v**4) % m in squares]
    return {'prime': prime, 'depth': depth, 'modulus': m,
            'v_unit_chart': first, 'u_unit_v_nonunit_chart': second,
            'obstructed': not first and not second}


def descent_candidates(a, b, *, places=((2, 3), (3, 2), (5, 1), (7, 1)), work_limit=100_000):
    candidates = squareclasses(a, b, work_limit=work_limit)
    places = tuple(tuple(p) for p in places)
    if len(places) > 16 or len(set(places)) != len(places):
        raise ValueError('at most 16 distinct finite places required')
    if any(len(t) != 2 or type(t[0]) is not int or not 2 <= t[0] <= 257 or not _prime(t[0])
           or type(t[1]) is not int or not 1 <= t[1] <= 16 for t in places):
        raise ValueError('places require a prime <=257 and depth in 1..16')
    # One total bound across every class and place, not a fresh limit per branch.
    work = len(candidates)*sum(2*p**k+p**k//p for p, k in places)
    if work > work_limit:
        raise WorkLimit('total descent chart budget exceeded')
    rows = []
    for d in candidates:
        local = [local_cover(a, b, d, p, depth, work_limit=work_limit) for p, depth in places]
        excluded = real_obstructed(a, b, d) or any(t['obstructed'] for t in local)
        rows.append({'d': d, 'cover': [d, a, b//d], 'real_obstructed': real_obstructed(a, b, d),
                     'local': local, 'status': 'excluded' if excluded else 'unresolved'})
    return {'schema': 'pp-two-torsion-squareclasses/1', 'curve': [a, b],
            'places': [list(p) for p in places], 'classes': rows,
            'survivors': [t['d'] for t in rows if t['status'] == 'unresolved'],
            'exceptional_points': ['O', '(0,0)'],
            'scope': 'complete candidate squareclasses for nonzero rational x; finite local exclusions only',
            'formal_verification': False}


def check_descent(packet, a=None, b=None, *, work_limit=100_000):
    if packet.get('schema') != 'pp-two-torsion-squareclasses/1':
        raise ValueError('invalid descent schema')
    source_a, source_b = packet['curve']
    if (a is not None and a != source_a) or (b is not None and b != source_b):
        raise ValueError('descent source binding failed')
    actual = descent_candidates(source_a, source_b, places=packet['places'], work_limit=work_limit)
    if actual != packet:
        raise ValueError('altered descent candidates or local tables')
    return True


def two_isogeny_rank_bound(a, b, *, places=((2,3),(3,2),(5,1),(7,1)), work_limit=100_000):
    """Native upper bound from both complete candidate supersets.

    The classical 2-isogeny descent identity is
    2^rank = |alpha(E(Q))|*|alpha(E'(Q))|/4. Each actual image is an
    elementary 2-group contained in its candidate superset, so floor(log2 K)
    bounds its dimension even when K is not a power of two. No Selmer
    completeness or kernel acceptance is inferred from these finite tests.
    """
    curve(a,b)
    left = descent_candidates(a,b,places=places,work_limit=work_limit)
    right = descent_candidates(-2*a,a*a-4*b,places=places,work_limit=work_limit)
    k, m = len(left['survivors']), len(right['survivors'])
    if not k or not m:
        raise AssertionError('candidate filter removed an identity squareclass')
    upper = (k.bit_length()-1)+(m.bit_length()-1)-2
    if upper < 0:
        raise AssertionError('candidate filters contradict the two-isogeny identity')
    return {'schema':'pp-two-isogeny-rank-bound/1','curve':[a,b],
            'isogenous_curve':[-2*a,a*a-4*b],'left':left,'right':right,
            'rank_upper_bound':upper,'rank_exact':0 if upper==0 else None,
            'scope':'rational Mordell-Weil rank upper bound via classical 2-isogeny descent identity',
            'formal_verification':False}


def check_rank_bound(packet, a=None, b=None, *, work_limit=100_000):
    if packet.get('schema') != 'pp-two-isogeny-rank-bound/1':
        raise ValueError('invalid rank-bound schema')
    source_a,source_b=packet['curve']
    if (a is not None and a!=source_a) or (b is not None and b!=source_b):
        raise ValueError('rank-bound source binding failed')
    actual=two_isogeny_rank_bound(source_a,source_b,places=packet['left']['places'],work_limit=work_limit)
    if actual!=packet:
        raise ValueError('rank bound or descent evidence altered')
    return True


def lift_cover(a, b, d, u, v, w, *, work_limit=100_000):
    if d not in squareclasses(a, b, work_limit=work_limit):
        raise ValueError('candidate squarefree d required')
    if any(type(t) is not int for t in (u, v, w)) or not u or v <= 0 or gcd(u, v) != 1:
        raise ValueError('primitive integral u,v,w with u!=0 and v>0 required')
    d, a, c = _cover(a, b, d)
    if w*w != d*u**4+a*u*u*v*v+c*v**4:
        raise ValueError('cover equation failed')
    x, y = Q(d*u*u, v*v), Q(d*u*w, v**3)
    if y*y != x*(x*x+a*x+b):
        raise AssertionError('cover transport identity failed')
    return {'x': str(x), 'y': str(y), 'd': d, 'u': u, 'v': v, 'w': w}


def recover_cover(a, b, x, y, *, work_limit=100_000):
    curve(a, b)
    x, y = rational(x), rational(y)
    if y*y != x*(x*x+a*x+b):
        raise ValueError('point does not lie on source curve')
    if not x:
        return {'exceptional': '(0,0)'}
    budget = Budget(work_limit)
    factors = _factor(abs(x.numerator)*x.denominator, budget)
    d = -1 if x < 0 else 1
    for p, e in factors:
        if e % 2:
            d *= p
    if b % d:
        raise AssertionError('rational point squareclass does not divide b')
    z = x/d
    u, v = isqrt(z.numerator), isqrt(z.denominator)
    if u*u != z.numerator or v*v != z.denominator:
        raise AssertionError('squareclass reconstruction failed')
    w = y*v**3/(d*u)
    if w.denominator != 1:
        raise AssertionError('rational square root of integer is nonintegral')
    return lift_cover(a, b, d, u, v, int(w), work_limit=work_limit)
