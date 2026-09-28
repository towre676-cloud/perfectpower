"""Complete, certified enumeration of hits in the rigid (Runge) branch.

Let F in Z[x] have degree dq (q >= 1) and leading coefficient b^d with b in Z, and let
Q = P/D (P in Z[x], D >= 1) be the truncated d-th root with remainder R = F - Q^d != 0,
deg R = r < (d-1)q.  (Theorem R in docs/RESEARCH_NOTES.md.)  Fix a threshold x0 with

    a(x0) = |b| - sum_{i<q} |Q_i| x0^(i-q) > 0,   C(x0) = sum_i |R_i| x0^(i-r),

and, when d is odd, C(x0) x0^r < a(x0)^d x0^(dq).  For every n >= x0 we then have
|Q(n)| >= a(x0) n^q > 0, |R(n)| <= C(x0) n^r, and (d odd) |R(n)| < |Q(n)|^d.  If F(n) = m^d,
pick the integer y in {m, -m} with y^d = F(n) and y Q(n) >= 0 (for odd d, y = m works because
F(n) has the sign of Q(n)).  Writing y = s Q(n) with s >= 0, |s - 1| <= |s^d - 1| gives

    |D y - P(n)| <= D |R(n)| / |Q(n)|^(d-1) <= D C(x0) x0^(r-(d-1)q) / a(x0)^(d-1) =: T(x0).

So t = D y - P(n) is an integer with |t| <= T(x0), and n is a root of

    G_t(x) = D^d F(x) - (P(x) + t)^d,

which is a nonzero integer polynomial: G_0 = D^d R, and for t != 0 its x^((d-1)q)
coefficient is -d t b^(d-1) D^(d-1) != 0 because r < (d-1)q.

The implementation scans 1..B0-1 directly, then walks dyadic blocks [x0, 2 x0): each block is
either scanned or handled by exact integer root isolation of G_t, |t| <= T(x0).  Since T(x0)
decreases to 0, eventually only G_0 = D^d R is left for the whole tail.  Every step is exact
integer/rational arithmetic, so the returned hit list is complete.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction

from .core import evaluate, hit_indices, integer_power_root, normalize, power, rigid_certificate
from .polyalg import integer_roots, subtract


@dataclass
class RungeEnumeration:
    coefficients: tuple[int, ...]
    d: int
    exact_identity: bool
    scan_below: int        # B0: indices 1..B0-1 were scanned directly
    max_t: int             # largest t-range |t| <= T used in a solved dyadic block
    hits: list[tuple[int, int]] = field(default_factory=list)   # (n, m), n >= 1
    polynomials_solved: int = 0
    tail_start: int = 1    # for n >= tail_start only t = 0 (roots of R) was possible


def runge_enumerate(coefficients, d: int, scan_limit: int = 10 ** 6,
                    solve_cost: int = 200) -> RungeEnumeration | None:
    """Return the complete hit set {n >= 1 : F(n) = m^d} for rigid F, or None if F is nonrigid.

    Raises ValueError if the direct-scan prefix would exceed scan_limit.
    """
    cert = rigid_certificate(coefficients, d)
    if cert is None:
        return None
    F = normalize(coefficients)
    Fi = tuple(int(c) for c in F)
    if cert.exact_identity:
        return RungeEnumeration(Fi, d, True, 1, 0, [], 0, 1)
    D = cert.denominator
    P = normalize(cert.root_numerators)                   # integer coefficients
    Q = normalize(Fraction(c, D) for c in cert.root_numerators)
    R = subtract(F, power(Q, d))
    q, r = len(Q) - 1, len(R) - 1
    b = abs(Q[-1])
    e = (d - 1) * q - r   # >= 1

    # Tail constants at a threshold x0 >= 1: for every x >= x0,
    #   |Q(x)| >= a(x0) x^q  with a(x0) = |b| - sum_{i<q} |Q_i| x0^(i-q),
    #   |R(x)| <= C(x0) x^r  with C(x0) = sum_i |R_i| x0^(i-r).
    def a_at(x0: int) -> Fraction:
        return b - sum(abs(Q[i]) * Fraction(1, x0 ** (q - i)) for i in range(q))

    def c_at(x0: int) -> Fraction:
        return sum(abs(R[i]) * Fraction(1, x0 ** (r - i)) for i in range(r + 1))

    def admissible(x0: int) -> bool:
        a = a_at(x0)
        if a <= 0:
            return False
        # odd d: |R| < |Q|^d forces the real d-th root of F(n) to share the sign of Q(n)
        return d % 2 == 0 or c_at(x0) * x0 ** r < a ** d * x0 ** (d * q)

    def t_tail(x0: int) -> int:
        """floor of D C(x0) x0^(r-(d-1)q) / a(x0)^(d-1): bounds |D y - P(n)| for all n >= x0."""
        return int(D * c_at(x0) / (a_at(x0) ** (d - 1) * Fraction(x0) ** e))

    B0 = 1
    while not admissible(B0):
        B0 *= 2
    if B0 - 1 > scan_limit:
        raise ValueError(f'direct scan prefix {B0 - 1} exceeds scan_limit')
    hits = dict(hit_indices(Fi, d, 0, B0 - 1))
    DdF = normalize([c * D ** d for c in F])

    def G(t: int):
        return subtract(DdF, power(normalize((P[0] + t,) + tuple(P[1:])), d))

    def record_roots(t: int, lo: int, hi: int | None):
        for n in integer_roots(G(t), lo=lo, hi=hi):
            m = integer_power_root(int(evaluate(F, n)), d)
            if m is not None:
                hits[n] = m

    # Dyadic blocks [lo, 2 lo): scan directly or solve G_t = 0 for |t| <= t_tail(lo),
    # whichever is cheaper.  Once t_tail(lo) = 0, only G_0 = D^d R remains on [lo, oo).
    solved, lo, max_t = 0, B0, 0
    while True:
        T = t_tail(lo)
        if T == 0:
            record_roots(0, lo, None)
            solved += 1
            break
        if lo <= solve_cost * (2 * T + 1):
            hits.update(hit_indices(Fi, d, 0, 2 * lo - 1, start=lo))
        else:
            max_t = max(max_t, T)
            for t in range(-T, T + 1):
                record_roots(t, lo, 2 * lo - 1)
                solved += 1
        lo *= 2
    return RungeEnumeration(Fi, d, False, B0, max_t, sorted(hits.items()), solved, lo)
