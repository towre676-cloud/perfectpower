"""Perfect-power hits of exponential sequences S(n) = c * a^n (Theorem E in the research notes).

For integers a >= 2 and c != 0, c a^n is a d-th power iff n lies in one residue class modulo
some L | d (or never).  Hence the hit density exists and equals 0 or 1/L.
"""
from __future__ import annotations

from fractions import Fraction
from math import gcd

from .arith import factorint


def exponential_progression(c: int, a: int, d: int):
    """(n0, L) with hits = {n >= 1 : n = n0 mod L}, or None if there are no hits.

    Valuation condition v_p(c) + n v_p(a) = 0 (mod d) for every prime p, plus the sign
    condition c > 0 when d is even (a >= 2 makes a^n > 0).
    """
    if a < 2 or c == 0 or d < 2:
        raise ValueError('need a >= 2, c != 0, d >= 2')
    if c < 0 and d % 2 == 0:
        return None
    fa, fc = factorint(a), factorint(c)
    n0, L = 0, 1                                  # current progression n = n0 mod L
    for p in sorted(set(fa) | set(fc)):
        va, vc = fa.get(p, 0), fc.get(p, 0)
        g = gcd(va, d)
        if vc % g:
            return None
        m = d // g                                # n va = -vc (mod d)  <=>  n = r (mod m)
        r = (-(vc // g) * pow(va // g, -1, m)) % m if m > 1 else 0
        # intersect n = n0 (mod L) with n = r (mod m); both moduli divide d
        G = gcd(L, m)
        if (r - n0) % G:
            return None
        lcm_ = L * m // G
        # solve n0 + L s = r (mod m)
        s = ((r - n0) // G * pow(L // G, -1, m // G)) % (m // G) if m // G > 1 else 0
        n0, L = (n0 + L * s) % lcm_, lcm_
    return (n0 if n0 >= 1 else n0 + L), L


def exponential_density(c: int, a: int, d: int) -> Fraction:
    prog = exponential_progression(c, a, d)
    return Fraction(0) if prog is None else Fraction(1, prog[1])


def exponential_hits(c: int, a: int, d: int, N: int) -> list[int]:
    prog = exponential_progression(c, a, d)
    if prog is None:
        return []
    n0, L = prog
    return list(range(n0, N + 1, L))
