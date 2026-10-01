"""Explicit unit-exponent bounds for cubic Thue equations in a totally real field of unit rank 2
(external certificates; the D = 72 script `thue_bound_d72.py` is the special case it reproduces).

**Setting.**  `K = Q(x)`, `x^3 = P x + Q`, with `O_K = Z[x]`.  Elements are coordinates
`(A, B, C) = A + B x + C x^2`.  A form `F = (c0, c1, c2, c3)` and a right side `M` are given, with
`phi = c0 θ` (θ a root of `F(X, 1)`) written in `O_K`, so that

    F(a, b) = M   <=>   N(c0 a - b phi) = c0^2 M          (`NormForm.det_mulMat`).

**Structural input (external, PARI `bnfcertify`).**  `h = 1`, `ε1, ε2` generate the units modulo
±1, and `bnfisintnorm` lists representatives `γ0` of every element of norm `c0^2 M` up to units.
So every solution has `γ := c0 a - b phi = ±γ0 ε1^e1 ε2^e2` for one listed `γ0`.
Write `H = max(|e1|, |e2|)`.

**The bound.**  Roots are isolated by exact rational sign checks, and every constant is an
`mpmath.iv` interval (900 bits) of which only the safe endpoint is kept: lower for `c`, upper for
`K1`, `b`, `K`, `A`, `C`, and `V0` with `(V0 + 1)^3 > 2 K1` checked on the enclosure.  The first
bound `H0` is accepted only when the lower end of `c H0 − log K − C (1 + log H0)` is positive.  For each `γ0` and each `i0`, the conjugate closest to `t = c0 a / b`:
1. `|γ_{i0}| <= 4 c0^2 |M| / (b^2 P)`, `|γ_j| >= |b| |φ_j - φ_{i0}| / 2`, `P = Π_{l≠i0} |φ_l - φ_{i0}|`.
2. Siegel: `Λ = (φ_{i0} - φ_j) γ_k / ((φ_{i0} - φ_k) γ_j) - 1` has `|Λ| <= K1 / |b|^3`,
   `K1 = 8 c0^2 |M| |φ_j - φ_k| / (P |φ_{i0} - φ_k| |φ_j - φ_{i0}|)`.  For `|b| > V0 = ⌊(2 K1)^{1/3}⌋`,
   `|Λ| <= 1/2` and `Λ0 = log(1 + Λ) = e1 l1 + e2 l2 + l3` has `|Λ0| <= 2 |Λ|`.
3. `log|γ_l| = log|b| + r_l` (`l = j, k`) with `r_l` in an explicit interval, so
   `(e1, e2) = M^{-1}(log|b| + r_j - log|γ0_j|, ...)` gives `log|b| >= (H - b')/a`.
4. Matveev (real case; Bugeaud–Mignotte–Siksek 2006, Thm 9.4), `n = 3`, degree `D = 6`:
   `H < H0`.
5. The direct maximum-exponent reduction (`DirectReduction.reduce`): for an integer `q` with
   `ε = ‖qμ‖ − M‖qκ‖ > 0`, `H ≤ log(qA/ε)/c`, bounding both exponents at once.  Each stage is
   recorded exactly (rational enclosures of `κ, μ`, `c ≥ cl`, `A ≤ Au`, and `(q, B, J)` with a
   Taylor certificate) and replayed by `perfectpower.reduction_check` and the Lean kernel.

Output per `(γ0, i0)`: `V0` and `H_reduced`.  The solutions with `|b| <= V0` are listed by an exact
search (`F(a, b) = M` with `b` fixed has its roots `a` within the Cauchy bound).
"""
from __future__ import annotations

from fractions import Fraction
import sys
from pathlib import Path

from mpmath import iv, mp, mpf

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'python'))
from perfectpower import reduction_check as RC  # noqa: E402

iv.prec = 900
mp.prec = 900


def _hi(x):
    return mpf(x.b)


def _lo(x):
    return mpf(x.a)


def _mid(x):
    return (mpf(x.a) + mpf(x.b)) / 2


class Field:
    """`x^3 = P x + Q`, three real roots."""

    def __init__(self, P: int, Q: int):
        self.P, self.Q = P, Q
        f = lambda t: t * t * t - P * t - Q          # noqa: E731
        R = 1 + abs(P) + abs(Q)
        grid = [Fraction(i, 64) for i in range(-64 * R, 64 * R + 1)]
        brackets = [(u, w) for u, w in zip(grid, grid[1:]) if f(u) == 0 or f(u) * f(w) < 0]
        assert len(brackets) == 3, 'needs three separated real roots'
        self.roots = [self._isolate(f, u, w) for u, w in brackets]

    @staticmethod
    def _isolate(f, lo, hi, bits=880):
        if f(lo) == 0:
            return iv.mpf([lo.numerator, lo.numerator]) / lo.denominator
        for _ in range(bits):
            mid = (lo + hi) / 2
            if f(mid) == 0:
                return iv.mpf(mid.numerator) / mid.denominator
            if f(lo) * f(mid) < 0:
                hi = mid
            else:
                lo = mid
        return iv.mpf([iv.mpf(lo.numerator) / lo.denominator, iv.mpf(hi.numerator) / hi.denominator])

    def conj(self, c):
        A, B, C = c
        return [A + B * d + C * d * d for d in self.roots]

    def mul(self, u, v):
        a, b, c = u
        d, e, f = v
        c0, c1, c2, c3, c4 = a * d, a * e + b * d, a * f + b * e + c * d, b * f + c * e, c * f
        # x^3 = P x + Q, x^4 = P x^2 + Q x
        return (c0 + self.Q * c3, c1 + self.P * c3 + self.Q * c4, c2 + self.P * c4)


def height(vals):
    """Absolute logarithmic height of an algebraic integer of degree 3, from its conjugates."""
    s = iv.mpf(0)
    for x in vals:
        ax = abs(x)
        s += iv.log(ax) if _lo(ax) > 1 else (iv.mpf(0) if _hi(ax) < 1 else iv.log(iv.mpf([1, _hi(ax)])))
    return s / 3


def matveev_C(A, n=3, D=6):
    return iv.mpf('1.4') * iv.mpf(30) ** (n + 3) * iv.mpf(n) ** iv.mpf('4.5') * D * D * (1 + iv.log(D)) * A[0] * A[1] * A[2]


def case(K: Field, c0: int, M: int, phi, gamma0, eps1, eps2, i0: int) -> dict:
    j, k = [i for i in range(3) if i != i0]
    PHI, G0, E1, E2 = K.conj(phi), K.conj(gamma0), K.conj(eps1), K.conj(eps2)
    cM = c0 * c0 * abs(M)
    P = abs(PHI[j] - PHI[i0]) * abs(PHI[k] - PHI[i0])
    K1 = 8 * cM * abs(PHI[j] - PHI[k]) / (P * abs(PHI[i0] - PHI[k]) * abs(PHI[j] - PHI[i0]))
    # V0 with (V0 + 1)^3 > 2 K1, verified on the interval enclosure (not on a rounded cube root)
    V0 = int(mp.floor(mp.cbrt(2 * _hi(K1))))
    while not _lo(iv.mpf(V0 + 1) ** 3) > _hi(2 * K1):
        V0 += 1
    l1 = iv.log(abs(E1[k] / E1[j]))
    l2 = iv.log(abs(E2[k] / E2[j]))
    l3 = iv.log(abs((PHI[i0] - PHI[j]) * G0[k] / ((PHI[i0] - PHI[k]) * G0[j])))
    Mx = [[iv.log(abs(E1[j])), iv.log(abs(E2[j]))], [iv.log(abs(E1[k])), iv.log(abs(E2[k]))]]
    det = Mx[0][0] * Mx[1][1] - Mx[0][1] * Mx[1][0]
    Minv = [[Mx[1][1] / det, -Mx[0][1] / det], [-Mx[1][0] / det, Mx[0][0] / det]]
    a = max(_hi(abs(Minv[0][0] + Minv[0][1])), _hi(abs(Minv[1][0] + Minv[1][1])))
    nrm = max(_hi(abs(Minv[0][0]) + abs(Minv[0][1])), _hi(abs(Minv[1][0]) + abs(Minv[1][1])))
    # |t - φ_{i0}| = |γ_{i0}| / |c0 ... | : |γ_{i0}| = |b| |φ_{i0} - t|, so |φ_{i0} - t| <= 4 cM / (|b|^3 P)
    tau = 4 * cM / (P * (V0 + 1) ** 3)
    R = mpf(0)
    for l in (j, k):
        dl = abs(PHI[l] - PHI[i0])
        lo_log, hi_log = iv.log(dl / 2), iv.log(dl + tau)
        lg = iv.log(abs(G0[l]))
        R = max(R, _hi(abs(lo_log - lg)), _hi(abs(hi_log - lg)))
    # From here on every constant is an upper or lower endpoint of an interval enclosure.  `a` and
    # `b` are exact mpf numbers that dominate the true row sums, so `c = 3/a` and
    # `K = 2 K1 exp(3b/a)` are the constants of a valid inequality; we enclose them and keep the
    # safe endpoint (c from below, K from above).
    b = _hi(iv.mpf(nrm) * iv.mpf(R))
    c_iv = iv.mpf(3) / iv.mpf(a)
    c2 = _lo(c_iv)
    Kc = _hi(2 * iv.mpf(_hi(K1)) * iv.exp(3 * iv.mpf(b) / iv.mpf(a)))
    h_e1, h_e2, h_g, h_p = height(E1), height(E2), height(G0), height(PHI)
    Dg = 6
    A1 = max(_hi(Dg * 2 * h_e1), _hi(abs(l1)), mpf('0.16'))
    A2 = max(_hi(Dg * 2 * h_e2), _hi(abs(l2)), mpf('0.16'))
    h3 = 2 * (2 * iv.mpf(_hi(h_p)) + iv.log(2)) + 2 * iv.mpf(_hi(h_g))
    A3 = max(_hi(Dg * h3), _hi(abs(l3)), mpf('0.16'))
    C = _hi(matveev_C([iv.mpf(A1), iv.mpf(A2), iv.mpf(A3)]))

    def _clears(H):
        # lower bound of c H − log K − C (1 + log H) on the enclosures (c from below, K, C from above)
        return _lo(iv.mpf(c2) * iv.mpf(H) - iv.log(iv.mpf(Kc)) - iv.mpf(C) * (1 + iv.log(iv.mpf(H)))) > 0
    H0 = mpf(2) * C / c2 * mp.log(C / c2)
    while not _clears(H0):
        H0 *= 2
    # the function is increasing for H > C / c, so clearing at H0 clears every larger H
    assert _lo(iv.mpf(H0)) > _hi(iv.mpf(C) / iv.mpf(c2))
    kap, mu = l1 / l2, l3 / l2
    Acoef = _hi(iv.mpf(Kc) / abs(l2))
    # rational enclosures (outward) of κ, μ, a lower bound for c and an upper bound for A
    enc = {'kl': _q_down(kap.a, 256), 'ku': _q_up(kap.b, 256), 'ml': _q_down(mu.a, 256),
           'mu': _q_up(mu.b, 256), 'cl': _q_down(c2, 64, slack=1), 'Au': _q_up(Acoef, 64, slack=1)}
    M0 = int(mp.ceil(H0))
    steps, Mb = [], M0
    for _ in range(16):
        st = _direct_step(enc, Mb, c2, Acoef)
        if st is None or st['B'] >= Mb:
            break
        steps.append(st)
        Mb = st['B']
    assert RC.chain_ok(enc, M0, steps) and RC.chain_end(M0, steps) == Mb
    return {'i0': i0, 'K1': mp.nstr(_hi(K1), 10), 'V0': V0, 'c2': mp.nstr(c2, 10), 'K': mp.nstr(Kc, 10),
            'A': [mp.nstr(A1, 8), mp.nstr(A2, 8), mp.nstr(A3, 8)], 'matveev_C': mp.nstr(C, 8),
            'H0': mp.nstr(H0, 8), 'M0': M0, 'enclosure': RC.enc_to_json(enc), 'steps': steps,
            'H_reduced': Mb}


def _q_exact(x):
    """An mpf as an exact Fraction."""
    sign, man, exp, _ = mpf(x)._mpf_
    v = Fraction(int(man)) * (Fraction(2) ** exp)
    return -v if sign else v


def _q_down(x, bits, slack=0):
    v = _q_exact(x) * 2 ** bits
    return Fraction(v.numerator // v.denominator - slack, 2 ** bits)


def _q_up(x, bits, slack=0):
    v = _q_exact(x) * 2 ** bits
    return Fraction(-((-v.numerator) // v.denominator) + slack, 2 ** bits)


def _direct_step(enc, M, c2, Acoef):
    """The direct maximum-exponent step (`DirectReduction.reduce`): a convergent denominator q of κ
    with ε = δ − M η > 0, and the least B with a Taylor certificate."""
    kmid = (enc['kl'] + enc['ku']) / 2
    p0, p1, q0, q1 = 0, 1, 1, 0
    y = kmid
    for _ in range(2000):
        ai = y.numerator // y.denominator
        p0, p1 = p1, ai * p1 + p0
        q0, q1 = q1, ai * q1 + q0
        if q1 > 10 ** 6 * M:
            eps = RC.delta_of(enc['ml'], enc['mu'], q1) - M * RC.eta_of(enc['kl'], enc['ku'], q1)
            if eps > 0:
                guess = int(mp.floor(mp.log(q1 * Acoef / mpf(eps.numerator) * eps.denominator) / c2))
                r = RC.best_step(enc, M, q1, guess)
                if r is not None:
                    return {'q': q1, 'B': r[0], 'J': r[1]}
        frac = y - ai
        if frac == 0:
            break
        y = 1 / frac
    return None


def evalF(F, a, b):
    c0, c1, c2, c3 = F
    return c0 * a ** 3 + c1 * a * a * b + c2 * a * b * b + c3 * b ** 3


def small_b(F, M, V):
    """All (a, b) with |b| <= V and F(a, b) = M, exactly: for fixed b, every root a satisfies the
    Cauchy bound |a| <= 1 + max(|c1 b|, |c2 b^2|, |c3 b^3 - M|) / |c0|."""
    c0, c1, c2, c3 = F
    out = []
    for b in range(-V, V + 1):
        Rb = 1 + max(abs(c1 * b), abs(c2 * b * b), abs(c3 * b ** 3 - M)) // abs(c0) + 1
        for a in range(-Rb, Rb + 1):
            if evalF(F, a, b) == M:
                out.append((a, b))
    return out


def bound(K: Field, F, M, phi, gammas, eps1, eps2) -> dict:
    """Every (γ0, i0) case, the combined (V0, H), and the small-|b| solutions."""
    cases = []
    for g, g0 in enumerate(gammas):
        for i0 in range(3):
            r = case(K, F[0], M, phi, g0, eps1, eps2, i0)
            r['gamma'] = g
            cases.append(r)
    V = max(c['V0'] for c in cases)
    return {'cases': cases, 'V0': V, 'H_bound': max(c['H_reduced'] for c in cases),
            'small_b_solutions': small_b(F, M, V)}
