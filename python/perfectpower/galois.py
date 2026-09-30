"""The Galois action behind the atlas: which roots of F are fixed, which are swapped, and why that
decides the shape of the hit set.

The squarefree decomposition F = c * prod_j S_j^j groups roots by multiplicity j.  The Galois
group of the splitting field permutes the roots of each S_j, so each layer splits into orbits:
rational roots (fixed points), conjugate pairs (an irreducible quadratic factor, group C2,
field Q(sqrt(disc))), cubic orbits (group A3 when the discriminant is a square, else S3), and
larger orbits.  For y^d = F(x) a root of multiplicity j carries t = d / gcd(d, j), constant on
the orbit, so the atlas profile {t_i} is a union of orbit profiles, and Theorem G's
S = sum (1 - 1/t_i) is a sum over orbits.

What this explains:
  * radical type: the single root with t >= 2 is Galois-fixed, so it is rational, alpha = u/v,
    and the hits are parametrized by (v n - u) = z0 w^t;
  * Pell type: the two roots with t = 2 form one conjugate pair (the norm form of Q(sqrt(D)),
    hence a Pell equation) or two fixed rational roots (a quadratic splitting over Q);
  * power type: no root carries an obstruction (every t = 1).

What it does not do: root symmetry does not decide whether an integer orbit is populated, nor
whether a curve of higher genus has a complete point list.  Factors of degree >= 4 without a
rational root or a quadratic factor found here are reported by degree only.
"""
from __future__ import annotations

from fractions import Fraction
from math import gcd, isqrt

from .arith import divisors, factorint
from .polyalg import degree, divmod_poly, poly, squarefree_decomposition


def _is_rational_square(q: Fraction) -> bool:
    if q < 0:
        return False
    n, d = q.numerator, q.denominator
    return isqrt(n) ** 2 == n and isqrt(d) ** 2 == d


def _squarefree_kernel(q: Fraction) -> int:
    """The squarefree integer D with Q(sqrt(q)) = Q(sqrt(D))."""
    n = q.numerator * q.denominator
    sign = -1 if n < 0 else 1
    out = 1
    for p_, e in factorint(abs(n)).items():
        if e % 2:
            out *= p_
    return sign * out


def _rational_roots(p) -> list[Fraction]:
    """Rational roots of a nonzero rational polynomial (rational root theorem)."""
    L = 1
    for c in p:
        L = L * c.denominator // gcd(L, c.denominator)
    q = [int(c * L) for c in p]
    while q and q[0] == 0:
        return sorted(set([Fraction(0)] + _rational_roots(poly(q[1:]))))
    a0, an = abs(q[0]), abs(q[-1])
    out = set()
    for num in divisors(a0):
        for den in divisors(an):
            for s in (1, -1):
                x = Fraction(s * num, den)
                v = Fraction(0)
                for c in reversed(p):
                    v = v * x + c
                if v == 0:
                    out.add(x)
    return sorted(out)


def _divide_linear(p, r: Fraction):
    quo, rem = divmod_poly(p, poly([-r, 1]))
    assert all(c == 0 for c in rem)
    return quo


def _monic(p):
    lc = p[-1]
    return tuple(Fraction(c) / lc for c in p)


def _orbits_of(p) -> list[dict]:
    """The Galois orbits of the roots of a squarefree rational polynomial."""
    p = _monic(p)
    orbits = []
    for r in _rational_roots(p):
        orbits.append({'size': 1, 'group': 'trivial', 'root': str(r)})
        p = _monic(_divide_linear(p, r))
    k = degree(p)
    if k <= 0:
        return orbits
    if k == 2:
        c, b = p[0], p[1]
        disc = b * b - 4 * c
        orbits.append({'size': 2, 'group': 'C2', 'factor': [str(x) for x in p],
                       'discriminant': str(disc),
                       'field': f'Q(sqrt({_squarefree_kernel(disc)}))'})
    elif k == 3:
        r_, q_, p_ = p[0], p[1], p[2]
        disc = (p_ * p_ * q_ * q_ - 4 * q_ ** 3 - 4 * p_ ** 3 * r_ - 27 * r_ * r_
                + 18 * p_ * q_ * r_)
        orbits.append({'size': 3, 'group': 'A3' if _is_rational_square(disc) else 'S3',
                       'factor': [str(x) for x in p], 'discriminant': str(disc)})
    else:
        # a product of one or more orbits; not factored further here
        orbits.append({'size': k, 'group': None, 'factor': [str(x) for x in p],
                       'note': 'roots without a rational root, one or more orbits (not factored)'})
    return orbits


def galois_profile(coefficients, d: int) -> dict:
    """Orbits of the Galois action on the roots of F, with the multiplicity j and the
    obstruction t = d / gcd(d, j) of each, and the reason for the atlas type."""
    F = poly(coefficients)
    if degree(F) <= 0:
        return {'orbits': [], 'explanation': 'constant: no roots'}
    _, parts = squarefree_decomposition(F)
    orbits = []
    for j, S in sorted(parts.items()):
        t = d // gcd(d, j)
        for o in _orbits_of(S):
            orbits.append({**o, 'multiplicity': j, 't': t})
    bad = [o for o in orbits if o['t'] != 1]
    nbad = sum(o['size'] for o in bad)
    if nbad == 0:
        why = 'power type: every root has t = 1, so no root obstructs; F is c * G^d'
    elif nbad == 1:
        why = ('radical type: the only obstructed root is fixed by Galois, hence rational '
               f"(alpha = {bad[0]['root']}); hits are parametrized through v n - u = z0 w^t")
    elif nbad == 2 and all(o['t'] == 2 for o in bad):
        if len(bad) == 1:
            why = ('Pell type: the two obstructed roots are one conjugate pair, the norm form of '
                   f"{bad[0]['field']}; square values come from a Pell equation")
        else:
            why = ('Pell type: the two obstructed roots are both rational (the quadratic splits '
                   'over Q)')
    else:
        S = sum(Fraction(o['size']) * (1 - Fraction(1, o['t'])) for o in bad)
        why = (f'finite type: over the obstructed roots S = sum (1 - 1/t) = {S} > 1, so '
               "chi = d'(1 - S) < 0 and Siegel gives finitely many hits (Theorem G)")
    return {'orbits': orbits, 'explanation': why}
