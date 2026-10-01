"""Exact replay of direct maximum-exponent reduction stages (`DirectReduction.lean`), stdlib only.

A stage is `(q, B, J)` under a case enclosure `(kl, ku, ml, mu, cl, Au)` and a previous bound `M`.
The definitions match `DirectReduction.pOf`, `etaOf`, `deltaOf`, `taylor` and `stepCheck` exactly,
so a stage that passes here is one the Lean kernel accepts (`chainCheck`), and conversely.
"""
from __future__ import annotations

from fractions import Fraction as Q
from math import factorial, floor


def p_of(kl: Q, ku: Q, q: int) -> int:
    return floor(q * (kl + ku) / 2 + Q(1, 2))


def eta_of(kl: Q, ku: Q, q: int) -> Q:
    p = p_of(kl, ku, q)
    return max(abs(q * kl - p), abs(q * ku - p))


def delta_of(ml: Q, mu: Q, q: int) -> Q:
    k = floor(q * ml)
    return min(q * ml - k, k + 1 - q * mu)


def taylor(x: Q, J: int) -> Q:
    return sum((x ** k / factorial(k) for k in range(J)), Q(0))


def step_ok(enc: dict, M: int, q: int, B: int, J: int) -> bool:
    kl, ku, ml, mu, cl, Au = (enc[k] for k in ('kl', 'ku', 'ml', 'mu', 'cl', 'Au'))
    eps = delta_of(ml, mu, q) - M * eta_of(kl, ku, q)
    return (q > 0 and cl >= 0 and Au >= 0 and kl <= ku and ml <= mu and eps > 0
            and q * Au / eps < taylor(cl * (B + 1), J))


def chain_end(M0: int, steps) -> int:
    M = M0
    for s in steps:
        M = s['B']
    return M


def chain_ok(enc: dict, M0: int, steps) -> bool:
    M = M0
    for s in steps:
        if not step_ok(enc, M, s['q'], s['B'], s['J']):
            return False
        M = s['B']
    return True


def enc_from_json(d: dict) -> dict:
    return {k: Q(int(d[k][0]), int(d[k][1])) for k in ('kl', 'ku', 'ml', 'mu', 'cl', 'Au')}


def enc_to_json(e: dict) -> dict:
    return {k: [str(v.numerator), str(v.denominator)] for k, v in e.items()}


def best_step(enc: dict, M: int, q: int, B_guess: int, max_terms: int = 4096):
    """The least `B >= B_guess - 2` (and its `J`) that `q` certifies from `M`, or None."""
    kl, ku, ml, mu, cl, Au = (enc[k] for k in ('kl', 'ku', 'ml', 'mu', 'cl', 'Au'))
    eps = delta_of(ml, mu, q) - M * eta_of(kl, ku, q)
    if eps <= 0:
        return None
    target = q * Au / eps
    for B in range(max(0, B_guess - 2), B_guess + 50):
        x = cl * (B + 1)
        total, term = Q(0), Q(1)
        for k in range(max_terms):
            total += term
            if total > target:
                return B, k + 1
            term = term * x / (k + 1)
            # past k + 1 >= 2x the tail is at most 2 * term: give up on this B
            if k + 1 >= 2 * x and total + 2 * term <= target:
                break
    return None
