"""Exact arithmetic oracles for general Weierstrass models (`PerfectPower/Weierstrass.lean`).

Coefficients are always the explicit tuple `(a1, a2, a3, a4, a6)` of
`y² + a1·xy + a3·y = x³ + a2·x² + a4·x + a6`.  The tau-crystal salvage review found an atlas whose
"11a1" traces belong to `(1, −1, 0, −10, −20)` instead of `(0, −1, 1, −10, −20)`: binding the
coefficient order is the point of this module.

* `complete_square`: `Y = 2y + a1·x + a3`, `Y² = quartRHS(x)` (`Weierstrass.complete_square`).
* `readout`: `y = (Y − a1·x − a3)/2`, integral whenever `Y² = quartRHS(x)` (`Weierstrass.parity_of_sq`).
* `ap`: `p + 1 − #E(F_p)` by exhaustive count over `F_p` (any prime `p`, including 2).
"""
from __future__ import annotations

MODEL_11A1 = (0, -1, 1, -10, -20)          # (a1, a2, a3, a4, a6)


def quart_rhs(a, x):
    a1, a2, a3, a4, a6 = a
    return 4 * x ** 3 + (a1 * a1 + 4 * a2) * x * x + (2 * a1 * a3 + 4 * a4) * x + a3 * a3 + 4 * a6


def on_curve(a, x, y):
    a1, a2, a3, a4, a6 = a
    return y * y + a1 * x * y + a3 * y == x ** 3 + a2 * x * x + a4 * x + a6


def complete_square(a, x, y):
    a1, _, a3, _, _ = a
    return 2 * y + a1 * x + a3


def readout(a, x, Y):
    a1, _, a3, _, _ = a
    assert Y * Y == quart_rhs(a, x)
    assert (Y - a1 * x - a3) % 2 == 0            # implied by the equation (parity_of_sq)
    return (Y - a1 * x - a3) // 2


def count_points(a, p):
    a1, a2, a3, a4, a6 = a
    n = 1                                         # the point at infinity
    for x in range(p):
        r = (x ** 3 + a2 * x * x + a4 * x + a6) % p
        for y in range(p):
            if (y * y + a1 * x * y + a3 * y - r) % p == 0:
                n += 1
    return n


def ap(a, p):
    return p + 1 - count_points(a, p)
