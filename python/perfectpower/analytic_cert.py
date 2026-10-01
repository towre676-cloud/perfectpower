"""Analytic certificates for `AnalyticBridge.analytic_of_cert`: an exact replay of the Lean
interval computation.

`PerfectPower/RatInterval.lean` and `PerfectPower/AnalyticBridge.lean` define, over `ℚ`, the
interval enclosures of one case (`caseCompute`) and its decidable side conditions (`caseOK`).  This
module computes the same rationals with `fractions.Fraction`, function by function and with the same
rounding (`rdn`, `rup` on the grid `2^-p`).  So a certificate accepted here is accepted by the
kernel, and the case data handed to Lean (`kl, ku, ml, mu, cl, Au, M0`, the reduction chain) are
derived from the values the kernel will recompute.

The one input that is not computed by these rules is Matveev's constant `Cm` for each case.  It comes
from the theorem of Matveev (Bugeaud–Mignotte–Siksek 2006, Thm 9.4, real case, `n = 3`, `D = 6`):

    log|Λ| > −1.4 · 30^6 · 3^4.5 · D² (1 + log D) (1 + log B) A₁A₂A₃,
    Aᵢ ≥ max(D h(αᵢ), |log αᵢ|, 0.16),

with the height bounds `h(α₁) ≤ 2h(ε₁)`, `h(α₂) ≤ 2h(ε₂)`,
`h(α₃) ≤ 2(2h(φ) + log 2) + 2h(γ₀)` (`h` of an algebraic integer is `(1/3) Σ log max(1, |σ|)`),
evaluated with the exact rational enclosures below and rounded up to an integer.  In Lean this enters as the named premise `MatveevCase … i`.
"""
from __future__ import annotations

import math
from fractions import Fraction as Fr

from . import reduction_check as RC

# ---------------------------------------------------------------- RatInterval, verbatim


def rdn(p, x):
    return Fr(math.floor(x * 2 ** p), 2 ** p)


def rup(p, x):
    return Fr(math.ceil(x * 2 ** p), 2 ** p)


def rnd(p, A):
    return (rdn(p, A[0]), rup(p, A[1]))


def ofQ(q):
    q = Fr(q)
    return (q, q)


def add(A, B):
    return (A[0] + B[0], A[1] + B[1])


def neg(A):
    return (-A[1], -A[0])


def sub(A, B):
    return add(A, neg(B))


def imin(a, b, c, d):
    return min(min(a * c, a * d), min(b * c, b * d))


def imax(a, b, c, d):
    return max(max(a * c, a * d), max(b * c, b * d))


def mul(A, B):
    return (imin(A[0], A[1], B[0], B[1]), imax(A[0], A[1], B[0], B[1]))


def inv(A):
    return (1 / A[1], 1 / A[0])


def div(A, B):
    return mul(A, inv(B))


def absI(A):
    if 0 <= A[0]:
        return A
    if A[1] <= 0:
        return neg(A)
    return (Fr(0), max(-A[0], A[1]))


def nz(A):
    return 0 < A[0] or A[1] < 0


def sumLo(p, J, z):
    z2, pw, s = rdn(p, z * z), z, Fr(0)
    for k in range(J):
        if k:
            pw = rdn(p, pw * z2)
        s += rdn(p, pw / (2 * k + 1))
    return s


def sumHi(p, J, z):
    z2, pw, s = rup(p, z * z), z, Fr(0)
    for k in range(J):
        if k:
            pw = rup(p, pw * z2)
        s += rup(p, pw / (2 * k + 1))
    pwJ = z if J == 0 else rup(p, pw * z2)
    return s + rup(p, pwJ / ((2 * J + 1) * (1 - z2)))


def blen(n):
    return n.bit_length() - 1 if n >= 2 else 0


def mOf(y):
    m = blen(abs(y.numerator)) - blen(y.denominator)
    return m if 1 <= y / Fr(2) ** m else m - 1


def red(y):
    m = mOf(y)
    return (m, y / Fr(2) ** m)


def zOf(w):
    return (w - 1) / (w + 1)


_L2 = {}


def log2I(p, J):
    if (p, J) not in _L2:
        _L2[(p, J)] = (2 * sumLo(p, J, Fr(1, 3)), 2 * sumHi(p, J, Fr(1, 3)))
    return _L2[(p, J)]


def mlog2(p, J, m):
    return mul(ofQ(m), log2I(p, J))


def logLo(p, J, y):
    m, w = red(y)
    return mlog2(p, J, m)[0] + 2 * sumLo(p, J, zOf(w))


def logHi(p, J, y):
    m, w = red(y)
    return mlog2(p, J, m)[1] + 2 * sumHi(p, J, zOf(w))


def logI(p, J, A):
    return (logLo(p, J, A[0]), logHi(p, J, A[1]))


def logOK(p, A):
    return (0 < A[0] and rup(p, Fr(1, 9)) < 1 and rup(p, zOf(red(A[1])[1]) ** 2) < 1
            and 1 <= red(A[0])[1] and 1 <= red(A[1])[1])


def expHi(p, m, r):
    v = rup(p, 1 / (1 - r / Fr(2) ** m))
    for _ in range(m):
        v = rup(p, v * v)
    return v


# ---------------------------------------------------------------- AnalyticBridge, verbatim


def caseCompute(p, J, em, Nq, V, B):
    lg = lambda A: logI(p, J, A)                       # noqa: E731
    dj = absI(sub(B['phj'], B['phi']))
    dk = absI(sub(B['phk'], B['phi']))
    djk = absI(sub(B['phj'], B['phk']))
    K1 = rnd(p, div(mul(ofQ(8 * Nq), djk), mul(mul(dj, dj), mul(dk, dk))))
    a1 = absI(div(B['e1k'], B['e1j']))
    a2 = absI(div(B['e2k'], B['e2j']))
    a3 = absI(div(mul(sub(B['phi'], B['phj']), B['gk']), mul(sub(B['phi'], B['phk']), B['gj'])))
    l1, l2, l3 = rnd(p, lg(a1)), rnd(p, lg(a2)), rnd(p, lg(a3))
    u1j, u2j = rnd(p, lg(absI(B['e1j']))), rnd(p, lg(absI(B['e2j'])))
    u1k, u2k = rnd(p, lg(absI(B['e1k']))), rnd(p, lg(absI(B['e2k'])))
    det = rnd(p, sub(mul(u1j, u2k), mul(u2j, u1k)))
    ad = absI(det)
    aQ = rup(p, max(div(absI(sub(u2k, u2j)), ad)[1], div(absI(sub(u1j, u1k)), ad)[1]))
    nQ = rup(p, max(div(add(absI(u2k), absI(u2j)), ad)[1], div(add(absI(u1j), absI(u1k)), ad)[1]))
    tau = rup(p, div(ofQ(4 * Nq / (Fr(V) + 1) ** 3), mul(dj, dk))[1])
    wj = (sub(lg(div(dj, ofQ(2))), lg(absI(B['gj'])))[0], sub(lg(add(dj, ofQ(tau))), lg(absI(B['gj'])))[1])
    wk = (sub(lg(div(dk, ofQ(2))), lg(absI(B['gk'])))[0], sub(lg(add(dk, ofQ(tau))), lg(absI(B['gk'])))[1])
    R = max(max(abs(wj[0]), abs(wj[1])), max(abs(wk[0]), abs(wk[1])))
    bb = rup(p, nQ * R)
    Au = rup(p, div(mul(ofQ(2), mul(K1, ofQ(expHi(p, em, 3 * bb / aQ)))), absI(l2))[1])
    return dict(dj=dj, dk=dk, K1=K1, a1=a1, a2=a2, a3=a3, l1=l1, l2=l2, l3=l3, u1j=u1j, u2j=u2j,
                u1k=u1k, u2k=u2k, det=det, aQ=aQ, nQ=nQ, tau=tau, wj=wj, wk=wk, R=R, bb=bb,
                kap=div(l1, l2), mu=div(l3, l2), Au=Au)


def caseOK(p, J, em, Nq, V, Cm, B, C, O=None):
    """The 48 checks of `caseOK`, in order; returns the list of failing indices (empty = accepted)."""
    O = O or caseCompute(p, J, em, Nq, V, B)
    lg = lambda A: logI(p, J, A)                       # noqa: E731
    M0 = Fr(C['M0'])
    checks = [
        nz(sub(B['phi'], B['phj'])), nz(sub(B['phi'], B['phk'])), nz(sub(B['phj'], B['phk'])),
        nz(B['e1j']), nz(B['e1k']), nz(B['e2j']), nz(B['e2k']), nz(B['gj']), nz(B['gk']),
        logOK(p, O['a1']), logOK(p, O['a2']), logOK(p, O['a3']),
        logOK(p, absI(B['e1j'])), logOK(p, absI(B['e2j'])), logOK(p, absI(B['e1k'])), logOK(p, absI(B['e2k'])),
        logOK(p, div(O['dj'], ofQ(2))), logOK(p, absI(B['gj'])), logOK(p, add(O['dj'], ofQ(O['tau']))),
        logOK(p, div(O['dk'], ofQ(2))), logOK(p, absI(B['gk'])), logOK(p, add(O['dk'], ofQ(O['tau']))),
        logOK(p, O['K1']), logOK(p, ofQ(M0)),
        nz(O['det']), nz(O['l2']), nz(mul(O['dj'], O['dk'])),
        nz(mul(mul(O['dj'], O['dj']), mul(O['dk'], O['dk']))), nz(absI(O['det'])), nz(absI(O['l2'])),
        nz(mul(sub(B['phi'], B['phk']), B['gj'])), nz(B['e1j']), nz(B['e2j']),
        0 < O['aQ'], 0 < Nq, 2 * O['K1'][1] <= (Fr(V) + 1) ** 3, 0 <= O['bb'],
        3 * O['bb'] / O['aQ'] / Fr(2) ** em < 1, 0 <= Cm, 1 <= M0, O['aQ'] * Cm / 3 <= M0,
        0 < 3 / O['aQ'] * M0 - lg(O['K1'])[1] - 3 * O['bb'] / O['aQ'] - Cm * (1 + lg(ofQ(M0))[1]),
        C['kl'] <= O['kap'][0], O['kap'][1] <= C['ku'], C['ml'] <= O['mu'][0], O['mu'][1] <= C['mu'],
        C['cl'] <= 3 / O['aQ'], O['Au'] <= C['Au']]
    assert len(checks) == 48
    return [n for n, ok in enumerate(checks) if not ok]


def sigQ(x, g):
    return g[0] + g[1] * x + g[2] * x * x


def rad(g, lo, hi):
    return (hi - lo) * (abs(Fr(g[1])) + 2 * abs(Fr(g[2])) * max(abs(lo), abs(hi)))


def sigI(g, lo, hi):
    return (sigQ(lo, g) - rad(g, lo, hi), sigQ(lo, g) + rad(g, lo, hi))


OJ, OK = (1, 0, 0), (2, 2, 1)


def baseOf(p, lo, hi, phi, g0, e1, e2, i):
    s = lambda g, l: rnd(p, sigI(g, lo[l], hi[l]))     # noqa: E731
    j, k = OJ[i], OK[i]
    return dict(phi=s(phi, i), phj=s(phi, j), phk=s(phi, k), gj=s(g0, j), gk=s(g0, k),
                e1j=s(e1, j), e1k=s(e1, k), e2j=s(e2, j), e2k=s(e2, k))


def cub(P, Q, x):
    return x ** 3 - P * x - Q


def brackets(P, Q, bits):
    """Three ordered dyadic brackets of width `2^-bits` with a strict sign change."""
    R = 1 + abs(P) + abs(Q)
    grid = [Fr(i, 64) for i in range(-64 * R, 64 * R + 1)]
    out = []
    for u, w in zip(grid, grid[1:]):
        if cub(P, Q, u) * cub(P, Q, w) < 0:
            lo, hi = u, w
            while hi - lo > Fr(1, 2 ** bits):
                mid = (lo + hi) / 2
                if cub(P, Q, mid) == 0:
                    raise ValueError('rational root')
                if cub(P, Q, lo) * cub(P, Q, mid) < 0:
                    hi = mid
                else:
                    lo = mid
            out.append((lo, hi))
    assert len(out) == 3 and out[0][1] < out[1][0] and out[1][1] < out[2][0]
    return [b[0] for b in out], [b[1] for b in out]


# ---------------------------------------------------------------- Matveev's constant


def _log_hi(p, J, x):
    """An upper bound for `log x`, `x > 0` rational (`logHi`)."""
    return logI(p, J, ofQ(x))[1]


def _sqrt3_hi():
    s = Fr(17320508075688773, 10 ** 16)
    while s * s < 3:
        s += Fr(1, 10 ** 16)
    return s


def _height_hi(p, J, encls):
    """An upper bound for the absolute logarithmic height of an algebraic integer of degree at most 3
    whose conjugates lie in the intervals `encls`: `(1/3) Σ log max(1, |σ|)`."""
    s = Fr(0)
    for A in encls:
        top = absI(A)[1]
        if top > 1:
            s += _log_hi(p, J, top)
    return s / 3


def matveev_constants(p, J, lo, hi, phi, g0, e1, e2):
    """Upper bounds (integers) for Matveev's constant of the three cases.  Exact rationals
    throughout: heights and `|log αᵢ|` from the enclosures of this module."""
    conj = lambda g: [rnd(p, sigI(g, lo[l], hi[l])) for l in range(3)]   # noqa: E731
    PHI, G0, E1, E2 = conj(phi), conj(g0), conj(e1), conj(e2)
    h_e1, h_e2, h_g, h_p = (_height_hi(p, J, X) for X in (E1, E2, G0, PHI))
    D = 6
    const = Fr(14, 10) * 30 ** 6 * 81 * _sqrt3_hi() * D * D * (1 + _log_hi(p, J, Fr(D)))
    out = []
    for i in range(3):
        j, k = OJ[i], OK[i]
        ls = [logI(p, J, absI(div(E1[k], E1[j]))), logI(p, J, absI(div(E2[k], E2[j]))),
              logI(p, J, absI(div(mul(sub(PHI[i], PHI[j]), G0[k]), mul(sub(PHI[i], PHI[k]), G0[j]))))]
        hs = [2 * h_e1, 2 * h_e2, 2 * (2 * h_p + _log_hi(p, J, Fr(2))) + 2 * h_g]
        A = [max(D * h, max(abs(L[0]), abs(L[1])), Fr(16, 100)) for h, L in zip(hs, ls)]
        C = const * A[0] * A[1] * A[2]
        out.append({'A': A, 'Cm': Fr(math.ceil(C))})
    return out


# ---------------------------------------------------------------- the certificate of one class


def _direct_step(enc, M, c2, Acoef):
    """The direct maximum-exponent step: a convergent denominator `q` of κ with
    `ε = δ − M η > 0`, and the least `B` with a Taylor certificate (`DirectReduction.reduce`)."""
    kmid = (enc['kl'] + enc['ku']) / 2
    p0, p1, q0, q1 = 0, 1, 1, 0
    y = kmid
    for _ in range(4000):
        ai = y.numerator // y.denominator
        p0, p1 = p1, ai * p1 + p0
        q0, q1 = q1, ai * q1 + q0
        if q1 > 10 ** 6 * M:
            eps = RC.delta_of(enc['ml'], enc['mu'], q1) - M * RC.eta_of(enc['kl'], enc['ku'], q1)
            if eps > 0:
                guess = int((math.log(q1) + math.log(Acoef) - math.log(eps)) / c2)
                r = RC.best_step(enc, M, q1, guess)
                if r is not None:
                    return {'q': q1, 'B': r[0], 'J': r[1]}
        frac = y - ai
        if frac == 0:
            break
        y = 1 / frac
    return None


def _first_M0(p, J, O, Cm):
    """The least `M₀` (after doubling, then bisection) passing the cutoff checks of `caseOK`."""
    aQ, bb = O['aQ'], O['bb']
    lK = logI(p, J, O['K1'])[1]

    def ok(M):
        M = Fr(M)
        return (1 <= M and aQ * Cm / 3 <= M and
                0 < 3 / aQ * M - lK - 3 * bb / aQ - Cm * (1 + logI(p, J, ofQ(M))[1]))
    hi = max(1, math.ceil(aQ * Cm / 3))
    while not ok(hi):
        hi *= 2
    lo = max(1, math.ceil(aQ * Cm / 3))
    if ok(lo):
        return lo
    while hi - lo > 1:          # ok(hi), not ok(lo); the check is monotone for M ≥ aQ·Cm/3
        mid = (lo + hi) // 2
        if ok(mid):
            hi = mid
        else:
            lo = mid
    return hi


def class_cert(P, Q, F, M, phi, g0, e1, e2, V0, p=192, extra_bits=48, em=12):
    """The certificate of one class: brackets, `p, J, em`, Matveev constants, the class bound `V`,
    and the three cases with their reduction chains.  Every check of `bracketsOK` and `caseOK` is
    replayed here and must pass."""
    J = math.ceil(p * math.log(2) / (2 * math.log(3))) + 2
    lo, hi = brackets(P, Q, p + extra_bits)
    mats = matveev_constants(p, J, lo, hi, phi, g0, e1, e2)
    Nq = Fr(abs(F[0] ** 2 * M))
    bases = [baseOf(p, lo, hi, phi, g0, e1, e2, i) for i in range(3)]
    # the class bound V: (V + 1)^3 ≥ 2 K1 for all three cases (K1 does not depend on V)
    V = V0
    for B in bases:
        K1hi = caseCompute(p, J, em, Nq, V, B)['K1'][1]
        while (Fr(V) + 1) ** 3 < 2 * K1hi:
            V += 1
    cases, report = [], []
    for i, B in enumerate(bases):
        O = caseCompute(p, J, em, Nq, V, B)
        Cm = mats[i]['Cm']
        M0 = _first_M0(p, J, O, Cm)
        enc = {'kl': rdn(p, O['kap'][0]), 'ku': rup(p, O['kap'][1]),
               'ml': rdn(p, O['mu'][0]), 'mu': rup(p, O['mu'][1]),
               'cl': rdn(64, 3 / O['aQ']), 'Au': rup(64, O['Au'])}
        c2 = float(enc['cl'])
        steps, Mb = [], M0
        for _ in range(16):
            st = _direct_step(enc, Mb, c2, enc['Au'])
            if st is None or st['B'] >= Mb:
                break
            steps.append(st)
            Mb = st['B']
        assert RC.chain_ok(enc, M0, steps) and RC.chain_end(M0, steps) == Mb
        C = dict(enc, M0=M0, steps=steps)
        bad = caseOK(p, J, em, Nq, V, Cm, B, C, O)
        assert not bad, f'case {i}: caseOK fails at checks {bad}'
        cases.append(C)
        width = max(O['kap'][1] - O['kap'][0], O['mu'][1] - O['mu'][0])
        report.append({'i0': i, 'Cm': int(Cm), 'A': [float(a) for a in mats[i]['A']],
                       'aQ': float(O['aQ']), 'c': float(3 / O['aQ']), 'bb': float(O['bb']),
                       'K1': float(O['K1'][1]), 'M0': M0, 'H_reduced': Mb,
                       'kappa_mu_width_log2': math.log2(width) if width else None,
                       'first_q_log2': math.log2(steps[0]['q']) if steps else None,
                       # the reduction sensitivity: the first step needs (width of κ, μ) · q · M₀ ≪ 1;
                       # this is −log₂ of that product
                       'precision_margin_bits': (-math.log2(width) - math.log2(steps[0]['q']) - math.log2(M0))
                       if steps and width else None,
                       'first_step_slack': float(RC.delta_of(enc['ml'], enc['mu'], steps[0]['q'])
                                                 - M0 * RC.eta_of(enc['kl'], enc['ku'], steps[0]['q']))
                       if steps else None})
    return {'lo': lo, 'hi': hi, 'p': p, 'J': J, 'em': em, 'Cm': [m['Cm'] for m in mats], 'V': V,
            'cases': cases, 'report': report}
