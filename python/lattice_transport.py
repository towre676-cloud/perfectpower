"""Mirror of `PerfectPower/LatticeTransport.lean`: complete solution sets through integer matrices of
any nonzero determinant, and the monic reduction of a binary cubic.

`transport(L, T, c)`: given a complete list `L` for `F = sM` and `F(Tz + c) = s G(z)`, the complete
list for `G = M` (filter by `adj(T)(x − c) ≡ 0 mod det T`, then divide).  `monic(F)` returns
`H = X³ + bX²Y + acXY² + a²dY³` with `H(au, v) = a² F(u, v)`.  The Lean theorems are
`complete_of_complete` and `monic_complete`; this file only executes the same arithmetic.
"""
from __future__ import annotations


def det(T):
    (p, q), (r, s) = T
    return p * s - q * r


def adj(T):
    (p, q), (r, s) = T
    return ((s, -q), (-r, p))


def ap(T, z):
    (p, q), (r, s) = T
    return (p * z[0] + q * z[1], r * z[0] + s * z[1])


def lat(T, c, x):
    D = det(T)
    w = ap(adj(T), (x[0] - c[0], x[1] - c[1]))
    return w[0] % D == 0 and w[1] % D == 0


def pull(T, c, x):
    D = det(T)
    w = ap(adj(T), (x[0] - c[0], x[1] - c[1]))
    return (w[0] // D, w[1] // D)


def transport(L, T, c=(0, 0)):
    assert det(T) != 0
    return sorted(pull(T, c, x) for x in L if lat(T, c, x))


def cubic(F, z):
    a, b, c, d = F
    u, v = z
    return a * u ** 3 + b * u * u * v + c * u * v * v + d * v ** 3


def monic(F):
    a, b, c, d = F
    return (1, b, a * c, a * a * d)


def disc(F):
    a, b, c, d = F
    return b * b * c * c - 4 * a * c ** 3 - 4 * b ** 3 * d - 27 * a * a * d * d + 18 * a * b * c * d
