"""An explicit exponent bound for the D = 72 residual Thue equation (external certificate).

    H(u, v) = -3u^3 + 9uv^2 - 2v^3 = ±1        (MORDELL_BRANCH.md §7.1)

Field `K = Q(δ)`, `δ^3 = 9δ + 6`, `O_K = Z[δ]` (discriminant 1944).  With `β = 6 - δ^2` and
`γ = -3u - βv` we have `N(γ) = 9 H(u, v)` (`NormForm.d72_det_delta`).

**Structural input (external, PARI `bnfcertify`):** `h = 1`; `ε1 = δ^2 - 3δ - 1` and
`ε2 = 2δ^2 - 1` generate the units modulo ±1; `(3) = p^3`, and `p^2 = (α)` with
`α = δ^2 - 3δ - 3` is the only ideal of norm 9.  Hence every solution has
`γ = ±α ε1^e1 ε2^e2`.  Write `H = max(|e1|, |e2|)`.

**The bound (this script; every constant is an interval, `mpmath.iv`; the roots are isolated by
exact rational sign checks).**  The steps:
1. Let `t = -3u/v` and `i0` the conjugate minimizing `|β_i - t|`.  Then
   `|γ_{i0}| <= 36/(|v|^2 P)`, `|γ_j| >= |v||β_j - β_{i0}|/2`.
2. Siegel's identity gives `Λ = -(β_j - β_k)γ_{i0}/((β_{i0} - β_k)γ_j)`, with `|Λ| <= K1/|v|^3`.
   For `|v| > V0 = floor((2 K1)^{1/3})` we have `|Λ| <= 1/2`, and
   `Λ0 = log|1 + Λ| = e1 l1 + e2 l2 + l3` satisfies `|Λ0| <= 2|Λ|`.
3. Two real embeddings give `(e1, e2) = M^{-1}(log|v| + r_j, log|v| + r_k)`, with the `r_l` in
   explicit intervals.  So `log|v| >= (H - b)/a`, and `|Λ0| <= K e^{-c2 H}`.
4. **Matveev** (2000, real case, as in Bugeaud–Mignotte–Siksek 2006, Thm 9.4), with `n = 3`, the
   Galois closure of degree `D = 6`, and `A_i >= max(D h, |log α_i|, 0.16)` from height bounds:
   `log|Λ0| > -C (1 + log H)`, hence `H < H0`.
5. **Reduction** (the Dujella–Pethő argument, valid for any integer `q`):
   `|e1 κ + e2 + μ| < A e^{-c2 |e1|}` and `||qμ|| - M ||qκ|| = ε > 0` give
   `|e1| < log(qA/ε)/c2`.  Since `H >= |e2|`, either `|e2| <= log(A)/c2` or `A e^{-c2 H} < 1` and
   `|e2| < |e1||κ| + |μ| + 1`.  This is iterated.

The output is `H <= Hred` for every solution with `|v| > V0`, for each choice of `i0`, plus the
finite list of `|v| <= V0`.  **This is an external certificate.**  Matveev's theorem, the height
bounds and the interval numerics are in Python, not Lean.  The structural input is PARI's.  The
finite search below the bound is exact, and is replayed in Lean
(`Generated/D72Residual.lean`).

Run: /opt/sagevenv/bin/python crosscheck/thue_bound_d72.py
Writes receipts/d72_thue_bound.json.
"""
import json
from fractions import Fraction
from math import isqrt
from pathlib import Path

from mpmath import iv, mp, mpf

ROOT = Path(__file__).resolve().parents[1]
iv.prec = 900
mp.prec = 900


def f(x):            # δ^3 - 9δ - 6, exact on rationals
    return x * x * x - 9 * x - 6


def isolate(lo, hi, bits=880):
    lo, hi = Fraction(lo), Fraction(hi)
    assert f(lo) * f(hi) < 0
    for _ in range(bits):
        mid = (lo + hi) / 2
        if f(mid) == 0:
            return iv.mpf([mid, mid])
        if f(lo) * f(mid) < 0:
            hi = mid
        else:
            lo = mid
    return iv.mpf([iv.mpf(lo.numerator) / lo.denominator, iv.mpf(hi.numerator) / hi.denominator])


DELTA = [isolate(-3, -2), isolate(-1, 0), isolate(3, 4)]


def conj(coeffs):    # A + B δ + C δ^2 at each embedding
    A, B, C = coeffs
    return [A + B * d + C * d * d for d in DELTA]


EPS1, EPS2, ALPHA = (-1, -3, 1), (-1, 0, 2), (-3, -3, 1)
BETA = conj((6, 0, -1))
E1, E2, AL = conj(EPS1), conj(EPS2), conj(ALPHA)


def ab(x):
    return abs(x)


def hi(x):
    return mpf(x.b)


def lo_(x):
    return mpf(x.a)


def mid(x):
    return (mpf(x.a) + mpf(x.b)) / 2


def height(vals):    # absolute logarithmic height of an algebraic integer of degree 3
    s = iv.mpf(0)
    for x in vals:
        ax = ab(x)
        s += iv.log(ax) if lo_(ax) > 1 else (iv.mpf(0) if hi(ax) < 1 else iv.log(iv.mpf([1, hi(ax)])))
    return s / 3


def matveev_C(A, n=3, D=6):
    return iv.mpf('1.4') * iv.mpf(30) ** (n + 3) * iv.mpf(n) ** iv.mpf('4.5') * D * D * (1 + iv.log(D)) * A[0] * A[1] * A[2]


def case(i0):
    j, k = [i for i in range(3) if i != i0]
    P = ab(BETA[j] - BETA[i0]) * ab(BETA[k] - BETA[i0])
    K1 = 72 * ab(BETA[j] - BETA[k]) / (P * ab(BETA[i0] - BETA[k]) * ab(BETA[j] - BETA[i0]))
    V0 = int(mp.floor(mp.cbrt(2 * hi(K1))))
    l1 = iv.log(ab(E1[k] / E1[j]))
    l2 = iv.log(ab(E2[k] / E2[j]))
    l3 = iv.log(ab((BETA[i0] - BETA[j]) * AL[k] / ((BETA[i0] - BETA[k]) * AL[j])))
    # (e1, e2) = Minv (log|v| + r_j, log|v| + r_k)
    M = [[iv.log(ab(E1[j])), iv.log(ab(E2[j]))], [iv.log(ab(E1[k])), iv.log(ab(E2[k]))]]
    det = M[0][0] * M[1][1] - M[0][1] * M[1][0]
    Minv = [[M[1][1] / det, -M[0][1] / det], [-M[1][0] / det, M[0][0] / det]]
    a = max(hi(ab(Minv[0][0] + Minv[0][1])), hi(ab(Minv[1][0] + Minv[1][1])))
    nrm = max(hi(ab(Minv[0][0]) + ab(Minv[0][1])), hi(ab(Minv[1][0]) + ab(Minv[1][1])))
    c9 = iv.cbrt(iv.mpf(9)) if hasattr(iv, 'cbrt') else iv.mpf(9) ** (iv.mpf(1) / 3)
    R = mpf(0)
    for l in (j, k):
        dl = ab(BETA[l] - BETA[i0])
        lo_log, hi_log = iv.log(dl / 2), iv.log(dl + c9)
        la = iv.log(ab(AL[l]))
        R = max(R, hi(ab(lo_log - la)), hi(ab(hi_log - la)))
    b = nrm * R
    c2 = 3 / mpf(a)
    K = 2 * hi(K1) * mp.exp(3 * b / a)
    # Matveev
    h_e1, h_e2, h_al, h_be = height(E1), height(E2), height(AL), height(BETA)
    Dg = 6
    A1 = max(Dg * 2 * hi(h_e1), hi(ab(l1)), mpf('0.16'))
    A2 = max(Dg * 2 * hi(h_e2), hi(ab(l2)), mpf('0.16'))
    h3 = 2 * (2 * hi(h_be) + mp.log(2)) + 2 * hi(h_al)
    A3 = max(Dg * h3, hi(ab(l3)), mpf('0.16'))
    C = hi(matveev_C([iv.mpf(A1), iv.mpf(A2), iv.mpf(A3)]))
    # H0: c2 H - log K - C (1 + log H) > 0 for H >= H0 (increasing once H > C/c2)
    H0 = mpf(2) * C / c2 * mp.log(C / c2)
    while not (c2 * H0 - mp.log(K) - C * (1 + mp.log(H0)) > 0):
        H0 *= 2
    assert H0 > C / c2
    # reduction: |e1 κ + e2 + μ| < A e^{-c2 |e1|}
    kap, mu = l1 / l2, l3 / l2
    Acoef = K / lo_(ab(l2))
    steps, Mb = [], H0
    for _ in range(12):
        # convergent denominators of κ (from the midpoint; any integer q is valid in the lemma)
        x = mid(kap)
        p0, p1, q0, q1 = 0, 1, 1, 0
        best = None
        y = x
        for _ in range(400):
            ai = int(mp.floor(y))
            p0, p1 = p1, ai * p1 + p0
            q0, q1 = q1, ai * q1 + q0
            if q1 > 10 ** 6 * Mb:
                qk = q1 * kap
                qm = q1 * mu
                dk = hi(ab(qk - mp.nint(mid(qk))))
                nm = mp.nint(mid(qm))
                dm = lo_(ab(qm - nm))
                dm = min(dm, lo_(ab(qm - nm - 1)), lo_(ab(qm - nm + 1)))
                eps = dm - Mb * dk
                if eps > 0:
                    best = (q1, eps)
                    break
            frac = y - ai
            if frac == 0:
                break
            y = 1 / frac
        if best is None:
            break
        q, eps = best
        X1 = mp.log(q * Acoef / eps) / c2
        # |e2|: since H >= |e2|, either |e2| <= T = log(A)/c2, or A e^{-c2 H} < 1 and then
        # |e2| < |e1||κ| + |μ| + 1
        T = max(mpf(0), mp.log(Acoef) / c2)
        newM = max(X1, T, X1 * hi(ab(kap)) + hi(ab(mu)) + 1)
        steps.append({'M': mp.nstr(Mb, 8), 'q_digits': len(str(q)), 'eps': mp.nstr(eps, 5),
                      'bound_e1': mp.nstr(X1, 8), 'new_H_bound': mp.nstr(newM, 8)})
        if newM >= Mb * mpf('0.999'):
            break
        Mb = mp.floor(newM)
    return {'i0': i0, 'K1': mp.nstr(hi(K1), 10), 'V0': V0, 'c2': mp.nstr(c2, 10), 'K': mp.nstr(K, 10),
            'A': [mp.nstr(A1, 8), mp.nstr(A2, 8), mp.nstr(A3, 8)], 'matveev_C': mp.nstr(C, 8),
            'H0': mp.nstr(H0, 8), 'reduction': steps, 'H_reduced': int(Mb)}


def small_v(V):
    """All (u, v) with 1 <= |v| <= V and H(u, v) = ±1 (|u| <= 2|v| + 1 by the leading term)."""
    out = []
    for v in range(-V, V + 1):
        if v == 0:
            continue
        for u in range(-2 * abs(v) - 1, 2 * abs(v) + 2):
            if abs(-3 * u ** 3 + 9 * u * v * v - 2 * v ** 3) == 1:
                out.append((u, v))
    return out


def main():
    cases = [case(i0) for i0 in range(3)]
    V = max(c['V0'] for c in cases)
    Hred = max(c['H_reduced'] for c in cases)
    out = {'label': 'EXTERNAL certificate: Matveev + interval numerics in Python, structural input from PARI '
                    '(bnfcertify); the finite search below the bound is exact and replayed in Lean',
           'equation': 'H(u,v) = -3u^3 + 9uv^2 - 2v^3 = ±1', 'field': 'x^3 - 9x - 6, O_K = Z[x], h = 1',
           'units': {'eps1': EPS1, 'eps2': EPS2}, 'alpha': ALPHA, 'cases': cases,
           'V0': V, 'small_v_solutions': small_v(V), 'H_bound': Hred,
           'statement': f'every solution with |v| > {V} has gamma = ±alpha eps1^e1 eps2^e2 with max(|e1|,|e2|) <= {Hred}'}
    (ROOT / 'receipts' / 'd72_thue_bound.json').write_text(json.dumps(out, indent=1) + '\n')
    for c in cases:
        print(f"i0={c['i0']}: V0={c['V0']} c2={c['c2']} Matveev C={c['matveev_C']} H0={c['H0']} -> "
              f"{[s['new_H_bound'] for s in c['reduction']]} -> H <= {c['H_reduced']}")
    print(f"V0 = {V}, small-|v| solutions: {out['small_v_solutions']}, H bound {Hred}")


if __name__ == '__main__':
    main()
