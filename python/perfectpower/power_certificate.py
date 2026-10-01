"""Exact checker for projector certificates (`PowerCertificate.lean`).

A certificate for `M` is `(P, ρ)` with `P² = P`, `MP = PM = P` and `‖M − P‖∞ ≤ ρ < 1`, all in exact
rationals (`int` or `Fraction`; floats are rejected).  Lean's `pow_eq_of_projector` then gives
`Mᵏ = P + (M − P)ᵏ` for `k ≥ 1`, and `norm_pow_sub_le_of` gives `‖Mᵏ − P‖ ≤ ρᵏ` in any normed ring
(here the induced ∞-norm, the maximum absolute row sum).  Adapted from the archive salvage review
(`docs/ARCHIVE_SALVAGE.md`).
"""
from fractions import Fraction


def mm(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]


def sub(a, b):
    return [[x - y for x, y in zip(ra, rb)] for ra, rb in zip(a, b)]


def norm_inf(a):
    """The induced ∞-norm: the maximum absolute row sum."""
    return max(sum(abs(x) for x in row) for row in a)


def check(m, p, rho):
    """True iff `(p, rho)` is a projector certificate for `m` (exact arithmetic only)."""
    n = len(m)
    if not n or len(p) != n or any(len(row) != n for row in m + p):
        return False
    if any(isinstance(x, bool) or not isinstance(x, (int, Fraction)) for row in m + p for x in row):
        return False
    if isinstance(rho, bool) or not isinstance(rho, (int, Fraction)) or not 0 <= rho < 1:
        return False
    return mm(p, p) == p and mm(m, p) == p and mm(p, m) == p and norm_inf(sub(m, p)) <= rho


def steps_for(rho, eps):
    """The least `k ≥ 1` with `ρᵏ ≤ ε` (exact)."""
    if any(isinstance(x, bool) or not isinstance(x, (int, Fraction)) for x in (rho, eps)):
        raise TypeError("rho and eps must be exact integers or fractions")
    if not 0 <= rho < 1 or eps <= 0:
        raise ValueError("require 0 <= rho < 1 and eps > 0")
    rho, eps = Fraction(rho), Fraction(eps)
    k, r = 1, rho
    while r > eps:
        k, r = k + 1, r * rho
    return k
