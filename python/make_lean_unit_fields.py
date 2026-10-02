"""Generate the unit-field certificates: `PerfectPower/Generated/Field756.lean` (the seven Thue
classes of the field of discriminant 756 and the curves `y^2 = x^3 - D`, `D = 7, 28, 63`) and
`PerfectPower/Generated/D72Unit.lean` (the `D = 72` residual `H(u, v) = ±1`).

Unit generation is **proved** for each field (`unitGen_proved`, from the certificate `ugCert`
built by `ug_cert` and checked by `UnitGenProof.ugCheck`), and so are the norm representatives
(`normRep_N_proved`, `NormRepProof`: explicit division), and so is the analytic statement
`analytic_i` (`analytic_i_proved`, `AnalyticBridge.analytic_of_cert`) from one named premise per
class:
- `matveev_i`: Matveev's lower bound for the three linear forms of the class
  (`AnalyticBridge.MatveevCase`), with the constants of the certificate `acert_i`.
The certificate (root brackets, precision, Matveev constants) and the cases are computed by
`perfectpower.analytic_cert`, an exact replay of `AnalyticBridge.caseCompute`/`caseOK`.  The kernel
checks the certificate, the direct-`H` reduction chains (`DirectReduction.chainCheck`), the norm
identity, the exponent box, the small-`b` search and, for curves, the branch transport.

Inputs: `receipts/field756_bound.json`, `receipts/d72_thue_bound.json` (`crosscheck/thue_bound*.py`),
`receipts/unit_basis_witness.json`, `receipts/norm_rep_localization.json`, `receipts/thue_graph.json`.
Before emitting, this script replays in exact arithmetic: every reduction chain
(`perfectpower.reduction_check`), the unit inverses, the box (hits equal PARI's lists: a positive
control), the small-`b` search, and the curve points against the Sage census.

Run: python3 python/make_lean_unit_fields.py
Writes the two Lean files, receipts/unit_fields_certificate.json and
receipts/analytic_certificates.json.
"""
from __future__ import annotations

import csv
import json
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower import analytic_cert as AC  # noqa: E402
from perfectpower import reduction_check as RC  # noqa: E402
from perfectpower.branch_descent import compile_curve, lean_args  # noqa: E402
from perfectpower.descent import W1, W2  # noqa: E402


def _i(x):
    return f'({x})' if x < 0 else str(x)


def z3_lean(t):
    return '(' + ', '.join(_i(v) for v in t) + ')'


def form_lean(F):
    return '(' + ', '.join(_i(c) for c in F) + ')'


def mat_lean(T):
    return f'(({_i(T[0][0])}, {_i(T[0][1])}), ({_i(T[1][0])}, {_i(T[1][1])}))'


def pairs_lean(L):
    return '[' + ', '.join(f'({_i(a)}, {_i(b)})' for a, b in L) + ']'


def mul(P, Q, x, y):
    a, b, c = x
    d, e, f = y
    c0, c1, c2, c3, c4 = a * d, a * e + b * d, a * f + b * e + c * d, b * f + c * e, c * f
    return (c0 + Q * c3, c1 + P * c3 + Q * c4, c2 + P * c4)


def inverse(P, Q, u):
    """Inverse of a unit by solving the 3x3 multiplication matrix exactly."""
    from fractions import Fraction
    cols = [mul(P, Q, u, e) for e in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]
    A = [[Fraction(cols[j][i]) for j in range(3)] + [Fraction(int(i == 0))] for i in range(3)]
    for c in range(3):
        r = next(r for r in range(c, 3) if A[r][c] != 0)
        A[c], A[r] = A[r], A[c]
        A[c] = [x / A[c][c] for x in A[c]]
        for r in range(3):
            if r != c:
                A[r] = [x - A[r][c] * y for x, y in zip(A[r], A[c])]
    inv = tuple(A[i][3] for i in range(3))
    assert all(x.denominator == 1 for x in inv)
    inv = tuple(int(x) for x in inv)
    assert mul(P, Q, u, inv) == (1, 0, 0)
    return inv


def pw(P, Q, x, n):
    r = (1, 0, 0)
    for _ in range(n):
        r = mul(P, Q, r, x)
    return r


def fam(P, Q, g0, e1, e1i, e2, e2i, B):
    def zp(x, xi, i):
        return pw(P, Q, x, i - B) if i >= B else pw(P, Q, xi, B - i)
    return [mul(P, Q, mul(P, Q, g0, zp(e1, e1i, i)), zp(e2, e2i, j))
            for i in range(2 * B + 1) for j in range(2 * B + 1)]


def enc(c0, phi, a, b):
    return (c0 * a - b * phi[0], -(b * phi[1]), -(b * phi[2]))


def _tdiv(x, y):          # Lean `Int.ediv` (Euclidean), as `/` on ℤ
    q = x // y
    if (x - q * y) < 0:
        q += 1 if y < 0 else -1
    return q


def dec(c0, phi, g):
    b = -_tdiv(g[1], phi[1]) if phi[2] == 0 else -_tdiv(g[2], phi[2])
    return (_tdiv(g[0] + b * phi[0], c0), b)


def evalF(F, a, b):
    c0, c1, c2, c3 = F
    return c0 * a ** 3 + c1 * a * a * b + c2 * a * b * b + c3 * b ** 3


def small_hits(F, M, V):
    out = []
    for b in range(-V, V + 1):
        S = abs(F[1] * b) + abs(F[2] * b * b) + abs(F[3] * b ** 3 - M) + 1
        for a in range(-S, S + 1):
            if evalF(F, a, b) == M:
                out.append((a, b))
    return out


def icbrt(n):
    if n < 0:
        return -icbrt(-n)
    x = int(round(n ** (1 / 3)))
    while x ** 3 > n:
        x -= 1
    while (x + 1) ** 3 <= n:
        x += 1
    return x



def nrm(P, Q, g):
    a, b, c = g
    return (a * ((a + P * c) * (a + P * c) - (P * b + Q * c) * b) - Q * c * (b * (a + P * c) - (P * b + Q * c) * c)
            + Q * b * (b * b - (a + P * c) * c))


def q_lean(x: Fraction) -> str:
    return f'(({x.numerator} : ℚ) / {x.denominator})'


def case_lean(c) -> str:
    e = RC.enc_from_json(c['enclosure'])
    steps = '[' + ', '.join(f"({s['q']}, {s['B']}, {s['J']})" for s in c['steps']) + ']'
    return (f"{{ kl := {q_lean(e['kl'])}, ku := {q_lean(e['ku'])},\n      ml := {q_lean(e['ml'])}, mu := {q_lean(e['mu'])},\n"
            f"      cl := {q_lean(e['cl'])}, Au := {q_lean(e['Au'])},\n      M0 := {c['M0']}, steps := {steps} }}")


def check_cases(cases, B):
    for c in cases:
        enc = RC.enc_from_json(c['enclosure'])
        assert RC.chain_ok(enc, c['M0'], c['steps']), 'reduction chain does not replay'
        assert RC.chain_end(c['M0'], c['steps']) == c['H_reduced'] <= B
    return len(cases), sum(len(c['steps']) for c in cases)


def _cub(P, Q, x):
    return x ** 3 - P * x - Q


def _sigq(x, g):
    return g[0] + g[1] * x + g[2] * x * x


def _encl(g, lo, hi):
    rad = (hi - lo) * (abs(g[1]) + 2 * abs(g[2]) * max(abs(lo), abs(hi)))
    v = abs(_sigq(lo, g))
    return v - rad, v + rad


def ug_cert(P, Q, e1, e2, bits=30, n=64, sbits=24, slab=False):
    """The unit-generation certificate checked by `UnitGenProof.ugCheck` (same definitions); with
    `slab`, its unit list covers the slab (`unitSlabSlice`) instead of the box."""
    c = ug_bounds(P, Q, e1, e2, bits, n, sbits)
    ba, bb, bc = c['ba'], c['bb'], c['bc']
    e1i, e2i = inverse(P, Q, e1), inverse(P, Q, e2)

    def zp(e, ei, k):
        return pw(P, Q, e, k) if k >= 0 else pw(P, Q, ei, -k)
    rep = {}
    for k in range(0, 13):
        for x in range(-k, k + 1):
            for y in range(-k, k + 1):
                g = mul(P, Q, zp(e1, e1i, x), zp(e2, e2i, y))
                for sg in (1, -1):
                    h = tuple(sg * c for c in g)
                    if h not in rep:
                        rep[h] = (sg, x, y)
    reps = []
    pts = slab_points(c) if slab else ((A, B, Cc) for A in range(-ba, ba + 1)
                                       for B in range(-bb, bb + 1) for Cc in range(-bc, bc + 1))
    for g in pts:
        if abs(nrm(P, Q, g)) == 1:
            assert g in rep, f'unit {g} has no small representation'
            reps.append(rep[g])
    return dict(c, reps=reps)


def ug_bounds(P, Q, e1, e2, bits=30, n=64, sbits=24):
    """The certificate of `ug_cert` without its unit list: brackets, witnesses, `Uᵢ` and the box."""
    import math
    R = 1 + abs(P) + abs(Q)
    grid = [Fraction(i, 64) for i in range(-64 * R, 64 * R + 1)]
    br = [(u, w) for u, w in zip(grid, grid[1:]) if _cub(P, Q, u) * _cub(P, Q, w) < 0]
    assert len(br) == 3, 'needs three separated real roots'
    brs = []
    for lo, hi in br:
        for _ in range(bits):
            m = (lo + hi) / 2
            if _cub(P, Q, lo) * _cub(P, Q, m) < 0:
                hi = m
            else:
                lo = m
        assert _cub(P, Q, lo) * _cub(P, Q, hi) < 0
        brs.append((lo, hi))
    (lo1, hi1), (lo2, hi2), (lo3, hi3) = brs

    def witness(p, q):
        s = Fraction(int(float(p) ** (1 / n) * 2 ** sbits), 2 ** sbits)
        while s ** n > p:
            s -= Fraction(1, 2 ** sbits)
        S = Fraction(int(float(q) ** (1 / n) * 2 ** sbits) + 1, 2 ** sbits)
        while S ** n < q:
            S += Fraction(1, 2 ** sbits)
        assert s > 0 and S > 0
        return s, S
    enc = {(r, i): _encl(e, *brs[i]) for r, e in ((1, e1), (2, e2)) for i in range(3)}
    assert all(v[0] > 0 for v in enc.values())
    wit = {(r, i): witness(*enc[(r, i)]) for r in (1, 2) for i in (0, 1)}
    l = lambda s: n * (1 - 1 / s)         # noqa: E731
    u = lambda S: n * (S - 1)             # noqa: E731

    def imin(a, b, c, d):
        return min(a * c, a * d, b * c, b * d)

    def imax(a, b, c, d):
        return max(a * c, a * d, b * c, b * d)
    (s11, S11), (s21, S21) = wit[(1, 0)], wit[(1, 1)]
    (s12, S12), (s22, S22) = wit[(2, 0)], wit[(2, 1)]
    dlo = imin(l(s11), u(S11), l(s22), u(S22)) - imax(l(s12), u(S12), l(s21), u(S21))
    dhi = imax(l(s11), u(S11), l(s22), u(S22)) - imin(l(s12), u(S12), l(s21), u(S21))
    assert dlo > 0 or dhi < 0, 'log determinant not separated from 0'
    mB = lambda r, i: max(enc[(r, i)][1], 1 / enc[(r, i)][0])   # noqa: E731
    U = []
    for i in range(3):
        sq = mB(1, i) * mB(2, i)
        Ui = Fraction(math.isqrt(int(sq * 2 ** 40)) + 1, 2 ** 20)
        assert Ui * Ui >= sq
        U.append(Ui)
    g12, g13, g23 = lo2 - hi1, lo3 - hi1, lo3 - hi2
    G = [g12 * g13, g12 * g23, g13 * g23]
    m = [max(abs(lo1), abs(hi1)), max(abs(lo2), abs(hi2)), max(abs(lo3), abs(hi3))]
    S = [max(abs(lo2 + lo3), abs(hi2 + hi3)), max(abs(lo1 + lo3), abs(hi1 + hi3)),
         max(abs(lo1 + lo2), abs(hi1 + hi2))]
    T = [m[1] * m[2], m[0] * m[2], m[0] * m[1]]
    cB = sum(U[i] / G[i] for i in range(3))
    bB = sum(S[i] * U[i] / G[i] for i in range(3))
    aB = sum(T[i] * U[i] / G[i] for i in range(3))
    bc, bb, ba = int(cB), int(bB), int(aB)        # floor: B < b + 1
    return {'lo1': lo1, 'hi1': hi1, 'lo2': lo2, 'hi2': hi2, 'lo3': lo3, 'hi3': hi3, 'n': n,
            's11': s11, 'S11': S11, 's21': s21, 'S21': S21, 's12': s12, 'S12': S12, 's22': s22, 'S22': S22,
            'U1': U[0], 'U2': U[1], 'U3': U[2], 'ba': ba, 'bb': bb, 'bc': bc}


def _ceil(x):
    return -((-x.numerator) // x.denominator)


def _floor(x):
    return x.numerator // x.denominator


def _aint(c, b, cc):
    """`UnitGenProof.slabLo`, `slabHi` (same definitions): the first coordinates allowed at `(b, cc)`."""
    los, his = [], []
    for i in (1, 2, 3):
        lo, hi, U = c[f'lo{i}'], c[f'hi{i}'], c[f'U{i}']
        g = (0, b, cc)
        sq = _sigq(lo, g)
        rad = (hi - lo) * (abs(b) + 2 * abs(cc) * max(abs(lo), abs(hi)))
        los.append(-U - sq - rad)
        his.append(U - sq + rad)
    return _ceil(max(los)), _floor(min(his))


def slab_points(c):
    """The triples `unitSlabSlice` enumerates, in its order."""
    for j in range(2 * c['bb'] + 1):
        for k in range(2 * c['bc'] + 1):
            b, cc = j - c['bb'], k - c['bc']
            l, h = _aint(c, b, cc)
            for a in range(l, h + 1):
                yield (a, b, cc)


def slab_cost(c, row_weight=3, exact=True):
    """Kernel work of the slab check: the lattice points plus `row_weight` per `(B, C)` row.
    `exact=False` estimates the intervals in floating point (for searching; the winner is recounted)."""
    import math as _m
    rows = (2 * c['bb'] + 1) * (2 * c['bc'] + 1)
    pts = 0
    if not exact:
        th = [float((c[f'lo{i}'] + c[f'hi{i}']) / 2) for i in (1, 2, 3)]
        U = [float(c[f'U{i}']) for i in (1, 2, 3)]
    for j in range(2 * c['bb'] + 1):
        for k in range(2 * c['bc'] + 1):
            b, cc = j - c['bb'], k - c['bc']
            if exact:
                l, h = _aint(c, b, cc)
            else:
                l = _m.ceil(max(-U[i] - b * th[i] - cc * th[i] ** 2 for i in range(3)))
                h = _m.floor(min(U[i] - b * th[i] - cc * th[i] ** 2 for i in range(3)))
            pts += max(0, h - l + 1)
    return pts + row_weight * rows, pts, rows


def box_size(c):
    return (2 * c['ba'] + 1) * (2 * c['bb'] + 1) * (2 * c['bc'] + 1)


def _zp(P, Q, e, k):
    return pw(P, Q, e, k) if k >= 0 else pw(P, Q, inverse(P, Q, e), -k)


def best_basis(P, Q, e1, e2, K=2):
    """Over `U ∈ GL₂(ℤ)` with entries in `[-K, K]`, the basis `ε'₁ = ε₁^{U₁₁} ε₂^{U₂₁}`,
    `ε'₂ = ε₁^{U₁₂} ε₂^{U₂₂}` (same group, `det U = ±1`) whose proved enumeration is cheapest:
    the slab cost when the box is large, the box size otherwise."""
    import itertools
    best = None
    mats = [m for m in itertools.product(range(-K, K + 1), repeat=4) if m[0] * m[3] - m[1] * m[2] in (1, -1)]
    mats.sort(key=lambda m: sum(map(abs, m)))     # the identity first, so the pruning bites early
    for a, b, cc, d in mats:
        f1 = mul(P, Q, _zp(P, Q, e1, a), _zp(P, Q, e2, cc))
        f2 = mul(P, Q, _zp(P, Q, e1, b), _zp(P, Q, e2, d))
        try:
            c = ug_bounds(P, Q, f1, f2)
        except AssertionError:
            continue
        bs = box_size(c)
        rows = (2 * c['bb'] + 1) * (2 * c['bc'] + 1)
        if best is not None and min(bs, 3 * rows) >= best[0][0]:
            continue                      # the rows alone cost more than the best so far
        cost = bs if bs <= 20000 else min(bs, slab_cost(c, exact=False)[0])
        key = (cost, (a, b, cc, d) != (1, 0, 0, 1), sum(map(abs, f1 + f2)))
        if best is None or key < best[0]:
            best = (key, (a, b, cc, d), f1, f2, c)
    _, U, f1, f2, c = best
    sc = slab_cost(c)
    bs = box_size(c)
    return {'U': U, 'e1': f1, 'e2': f2, 'method': 'box' if bs <= 20000 or bs <= sc[0] else 'slab',
            'cost': min(bs, sc[0]) if bs > 20000 else bs, 'box': bs, 'slab_cost': sc[0], 'slab_points': sc[1],
            'slab_rows': sc[2], 'bounds': (c['ba'], c['bb'], c['bc'])}


def find_units(P, Q, schedule=((12, 200), (20, 600), (30, 2000), (45, 50000))):
    """`find_units_in` over a growing search, first success."""
    for R, nmax in schedule:
        u = find_units_in(P, Q, R, nmax)
        if u:
            return u
    return None


def find_units_in(P, Q, R=12, nmax=200):
    """A pair of independent units of `ℤ[x]`, `x³ = Px + Q`, of least regulator among the quotients
    `g h#/N(h)` of small elements of equal norm.  Not a proof: `UnitGenProof` decides whether the pair
    generates (a missing unit makes the enumeration fail)."""
    import itertools
    import math as _m
    from collections import defaultdict

    def adj(g):
        A, B, C = g
        return ((A + P * C) ** 2 - (P * B + Q * C) * B, Q * C * C - A * B, B * B - A * C - P * C * C)
    lim = 1 + abs(P) + abs(Q)
    grid = [Fraction(i, 64) for i in range(-64 * lim, 64 * lim + 1)]
    roots = []
    for u, w in zip(grid, grid[1:]):
        if _cub(P, Q, u) * _cub(P, Q, w) < 0:
            u, w = float(u), float(w)
            for _ in range(80):
                m = (u + w) / 2
                if (u ** 3 - P * u - Q) * (m ** 3 - P * m - Q) <= 0:
                    w = m
                else:
                    u = m
            roots.append(u)
    assert len(roots) == 3

    def logv(g):
        return [_m.log(abs(g[0] + g[1] * r + g[2] * r * r)) for r in roots]
    byN = defaultdict(list)
    for g in itertools.product(range(-R, R + 1), repeat=3):
        n = abs(nrm(P, Q, g))
        if 0 < n <= nmax and len(byN[n]) < 400:
            byN[n].append(g)
    units = set()
    for n, gs in byN.items():
        for i, g in enumerate(gs):
            for h in gs[i + 1:]:
                q = mul(P, Q, g, adj(h))
                nh = nrm(P, Q, h)
                if all(x % nh == 0 for x in q):
                    u = tuple(x // nh for x in q)
                    if u not in ((1, 0, 0), (-1, 0, 0)):
                        units.add(u)
    us = sorted(units, key=lambda u: (sum(abs(x) for x in logv(u)), u))[:80]
    best = None
    for i, a in enumerate(us):
        for b in us[i + 1:]:
            la, lb = logv(a), logv(b)
            d = abs(la[0] * lb[1] - la[1] * lb[0])
            # totally real cubic regulators exceed 0.5; smaller values are dependent pairs in floating point
            if d > 0.3 and (best is None or d < best[0] - 1e-9):
                best = (d, a, b)
    return (best[1], best[2], best[0]) if best else None


def ug_lean(c):
    rs = '[' + ', '.join(f'({_i(s)}, {_i(x)}, {_i(y)})' for s, x, y in c['reps']) + ']'
    f = [f'{k} := {q_lean(c[k])}' for k in ('lo1', 'hi1', 'lo2', 'hi2', 'lo3', 'hi3', 's11', 'S11', 's21',
                                             'S21', 's12', 'S12', 's22', 'S22', 'U1', 'U2', 'U3')]
    return ('{ ' + ',\n    '.join(f + [f"n := {c['n']}", f"ba := {c['ba']}", f"bb := {c['bb']}",
                                    f"bc := {c['bc']}", f'reps := {rs}']) + ' }')


def field_preamble(P, Q, e1, e2, witness):
    e1i, e2i = inverse(P, Q, e1), inverse(P, Q, e2)
    w = next(f for f in witness['fields'] if (f['P'], f['Q']) == (P, Q))
    a, b, c = w['coordinate_box']
    cands = [tuple(x['coordinates']) for x in w['candidates']]
    # the finite part replayed here too: every box triple of norm ±1 is a candidate
    for x in range(-a, a + 1):
        for y in range(-b, b + 1):
            for z in range(-c, c + 1):
                if abs(nrm(P, Q, (x, y, z))) == 1:
                    assert (x, y, z) in cands
    for g in cands:
        if g not in ((1, 0, 0), (-1, 0, 0)):
            assert any(x['coordinates'] == list(g) and x['excluded_from_centered_domain'] for x in w['candidates'])
    cert = ug_cert(P, Q, e1, e2)
    text = (f'/-- `ε₁`. -/\ndef e1 : Z3 := {z3_lean(e1)}\n/-- `ε₁⁻¹`. -/\ndef e1i : Z3 := {z3_lean(e1i)}\n'
            f'/-- `ε₂`. -/\ndef e2 : Z3 := {z3_lean(e2)}\n/-- `ε₂⁻¹`. -/\ndef e2i : Z3 := {z3_lean(e2i)}\n\n'
            f'theorem e1_inv : mul {P} {Q} e1 e1i = (1, 0, 0) := by decide\n'
            f'theorem e2_inv : mul {P} {Q} e2 e2i = (1, 0, 0) := by decide\n\n'
            f'/-- The unit-generation statement for `ℤ[x]`, `x³ = {P}x + {Q}`: every unit is `±ε₁^a ε₂^b`. -/\n'
            f'def unitGen : Prop := UnitPremises.UnitGen {P} {Q} e1 e1i e2 e2i\n\n'
            f'/-- The unit-generation certificate (`UnitGenProof.UGCert`): root brackets, log witnesses, '
            f'the bounds `Uᵢ`, the box `{cert["ba"]}, {cert["bb"]}, {cert["bc"]}` and the {len(cert["reps"])} units in it '
            f'as `±ε₁^x ε₂^y`. -/\n'
            f'def ugCert : UnitGenProof.UGCert :=\n  {ug_lean(cert)}\n\n'
            f'/-- **Unit generation, proved** (`UnitGenProof.unitGen_of_cert`, certificate checked by the '
            f'kernel).  This was a premise; it is now a theorem. -/\n'
            f'theorem unitGen_proved : unitGen :=\n'
            f'  UnitGenProof.unitGen_of_cert {P} {Q} e1 e1i e2 e2i ugCert (by decide +kernel)\n')
    return text, e1i, e2i, {'witness_box': [a, b, c], 'witness_triples': (2*a+1)*(2*b+1)*(2*c+1),
                            'witness_candidates': len(cands),
                            'lean_box': [cert['ba'], cert['bb'], cert['bc']],
                            'lean_triples': (2*cert['ba']+1)*(2*cert['bb']+1)*(2*cert['bc']+1),
                            'lean_units': len(cert['reps'])}


def _support(N):
    r = s = 0
    m = abs(N)
    while m % 2 == 0:
        m //= 2
        r += 1
    while m % 3 == 0:
        m //= 3
        s += 1
    assert m == 1, f'norm {N} is not supported on 2 and 3'
    return r, s


def norm_rep_block(nname, P, Q, N, g0, labels):
    """The `NormRep` statement and its proof (`NormRepProof`: explicit division)."""
    assert nrm(P, Q, g0) == N
    if (P, Q) == (6, 2):
        r, s = _support(N)
        side = 'Or.inl' if N > 0 else 'Or.inr'
        proof = f"NormRepProof.normRep756 {_i(N)} {z3_lean(g0)} {r} {s} ({side} (by norm_num)) (by decide)"
        how = f"`{_i(N)} = ±2^{r} 3^{s}`: divide by `x` and `1 + x` (`NormRepProof.normRep756`)"
    elif (P, Q, N, tuple(g0)) == (9, 6, 9, (-3, -3, 1)):
        proof = "NormRepProof.normRep_d72"
        how = "divide by `α` (`NormRepProof.normRep_d72`)"
    else:
        raise SystemExit(f'no NormRep proof for {(P, Q, N, g0)}')
    return (f"/-- The norm-representative statement (used by {', '.join(labels)}): every element of norm "
            f"{N} is `{list(g0)}` times a unit. -/\n"
            f"def {nname} : Prop := UnitPremises.NormRep {P} {Q} {_i(N)} [{z3_lean(g0)}]\n\n"
            f"/-- **Proved** by explicit division: {how}. -/\n"
            f"theorem {nname}_proved : {nname} :=\n  {proof}\n\n")


def analytic_cert(P, Q, F, M, phi, g0, e1, e2, V0):
    """The analytic certificate of a class (`perfectpower.analytic_cert`, an exact replay of
    `AnalyticBridge.caseCompute`/`caseOK`), with its cases in the receipt format."""
    r = AC.class_cert(P, Q, F, M, phi, g0, e1, e2, V0)
    r['cases_json'] = [{'enclosure': RC.enc_to_json({k: c[k] for k in ('kl', 'ku', 'ml', 'mu', 'cl', 'Au')}),
                        'M0': c['M0'], 'steps': c['steps'], 'H_reduced': RC.chain_end(c['M0'], c['steps'])}
                       for c in r['cases']]
    return r


def _cert_json(label, cert):
    q = lambda x: f'{x.numerator}/{x.denominator}'           # noqa: E731
    return {'class': label, 'p': cert['p'], 'J': cert['J'], 'em': cert['em'], 'V': cert['V'],
            'lo': [q(x) for x in cert['lo']], 'hi': [q(x) for x in cert['hi']],
            'Cm': [int(x) for x in cert['Cm']], 'cases': cert['cases_json'], 'report': cert['report']}


def _vec(xs):
    return '![' + ', '.join(q_lean(Fraction(x)) for x in xs) + ']'


def analytic_block(name, P, Q, F, M, phi, g0, cert, V, label):
    """The certificate, the Matveev premise and the proof of `analytic_{name}`."""
    a = (f"/-- The analytic certificate of {label} (`python/perfectpower/analytic_cert.py`): root brackets, "
         f"precision `2^-{cert['p']}`, `{cert['J']}` series terms, `{cert['em']}` squarings, Matveev's constants. -/\n"
         f"def acert_{name} : AnalyticBridge.ACert :=\n"
         f"  {{ lo := {_vec(cert['lo'])},\n    hi := {_vec(cert['hi'])},\n"
         f"    p := {cert['p']}, J := {cert['J']}, em := {cert['em']},\n    Cm := {_vec(cert['Cm'])} }}\n\n"
         f"/-- **Matveev's lower bound** for the three cases of {label} (`AnalyticBridge.MatveevCase`: "
         f"Bugeaud–Mignotte–Siksek 2006, Thm 9.4, real case, `n = 3`, `D = 6`, with the constants "
         f"`acert_{name}.Cm`).  The one premise of this class; not proved in Lean. -/\n"
         f"def matveev_{name} : Prop :=\n  ∀ i, AnalyticBridge.MatveevCase {P} {Q} acert_{name} {z3_lean(phi)} "
         f"{z3_lean(g0)} e1 e2 i\n\n")
    nq = f"((|({_i(F[0])} : ℤ) ^ 2 * {_i(M)}| : ℤ) : ℚ)"
    for i in range(3):
        a += (f"theorem caseOK_{name}_{i} : AnalyticBridge.caseOK acert_{name}.p acert_{name}.J acert_{name}.em\n"
              f"    {nq} {V} (acert_{name}.Cm {i})\n"
              f"    (AnalyticBridge.baseOf acert_{name} {z3_lean(phi)} {z3_lean(g0)} e1 e2 {i}) "
              f"case_{name}_{i} = true := by decide +kernel\n\n")
    a += (f"/-- **The analytic premise of {label}, proved from Matveev's bound** "
          f"(`AnalyticBridge.analytic_of_cert`: Siegel's identity, the conjugate estimates, the inverse log "
          f"matrix and the Matveev cutoff, with every interval check evaluated by the kernel). -/\n"
          f"theorem analytic_{name}_proved (hM : matveev_{name}) : analytic_{name} :=\n"
          f"  AnalyticBridge.analytic_of_cert {form_lean(F)} {_i(M)} {P} {Q} {z3_lean(phi)} {z3_lean(g0)} "
          f"e1 e1i e2 e2i {V} acert_{name}\n"
          f"    case_{name}_0 case_{name}_1 case_{name}_2 e1_inv e2_inv (fun a b => by simp only [UnitPremises.nrm, enc, evalF]; ring)\n"
          f"    (by decide +kernel) (by decide) (by decide)\n"
          f"    (fun i => by fin_cases i; exacts [caseOK_{name}_0, caseOK_{name}_1, caseOK_{name}_2]) hM\n\n")
    return a


def class_block(name, P, Q, F, M, phi, g0, cases, B, V, L, label, nname, neg_of=None, cert=None):
    """One class theorem.  With `neg_of`, the class is the negated target of class `neg_of`: its
    representatives and cases are `negReps reps_{neg_of}`, and its premises are transported."""
    assert nrm(P, Q, g0) == F[0] ** 2 * M
    ncases, nsteps = check_cases(cases, B)
    if neg_of is None:
        assert len(cases) == 3
        cdefs = ''.join(f"/-- Case {k} of {label}: the closest conjugate is `σ{k}`. -/\n"
                        f"def case_{name}_{k} : UnitPremises.Case :=\n  {case_lean(c)}\n\n"
                        for k, c in enumerate(cases))
        cs = ', '.join(f'case_{name}_{k}' for k in range(3))
        reps = (cdefs +
                f"/-- The analytic cases of {label}: {ncases} cases, {nsteps} reduction steps, final bound {B}. -/\n"
                f"def reps_{name} : List (Z3 × List UnitPremises.Case) :=\n  [({z3_lean(g0)}, [{cs}])]\n\n"
                f"/-- The analytic statement for {label} (`UnitPremises.Analytic`), proved below from "
                f"`matveev_{name}`. -/\n"
                f"def analytic_{name} : Prop :=\n  UnitPremises.Analytic {form_lean(F)} {_i(M)} {P} {Q} {z3_lean(phi)} "
                f"e1 e1i e2 e2i {V} reps_{name}\n\n")
        reps += analytic_block(name, P, Q, F, M, phi, g0, cert, V, label)
        reps += (f"/-- Negative control: every chain of {label} with its final bound lowered by one is rejected "
                 f"by the kernel. -/\n"
                 f"theorem forged_rejected_{name} : UnitPremises.forgedRejectedB reps_{name} = true := by decide +kernel\n\n")
        hyps = f"(hM : matveev_{name})"
        hN, hA = f'{nname}_proved', f'analytic_{name}_proved hM'
    else:
        reps = (f"/-- The representatives and cases of {label}: those of `{neg_of}`, negated. -/\n"
                f"def reps_{name} : List (Z3 × List UnitPremises.Case) := UnitPremises.negReps reps_{neg_of}\n\n")
        hyps = f"(hM : matveev_{neg_of})"
        hN = 'UnitPremises.normRep_neg_of (reps := reps_' + neg_of + f') {nname}_proved'
        hA = f'UnitPremises.analytic_neg_of (analytic_{neg_of}_proved hM)'
    note = '' if neg_of is None else f"  Its norm and analytic premises are those of `{neg_of}`, transported by sign. "
    return (reps +
            f"/-- **{label}, complete under Matveev's bound**: `{list(F)}` takes the value {M} exactly at "
            f"{len(L)} point(s).{note}  Kernel-checked: the analytic certificate, the reduction chains "
            f"(to `H ≤ {B}`), the norm identity, the box (`{2 * B + 1}²` elements) and the search `|b| ≤ {V}`. -/\n"
            f"theorem class_{name} {hyps} (u v : ℤ) :\n"
            f"    evalF {form_lean(F)} u v = {_i(M)} ↔ (u, v) ∈ ({pairs_lean(L)} : List (ℤ × ℤ)) :=\n"
            f"  thue_list {form_lean(F)} {_i(M)} {P} {Q} {z3_lean(phi)} (reps_{name}.map Prod.fst) e1 e1i e2 e2i {B} {V} "
            f"{pairs_lean(L)}\n    (by decide) (by decide)\n"
            f"    (UnitPremises.extBound_of _ _ _ _ _ _ _ _ _ _ _ reps_{name} unitGen_proved ({hN})\n"
            f"      (fun a b => by simp only [UnitPremises.nrm, enc, evalF]; ring) ({hA}) (by decide +kernel))\n"
            f"    (by decide +kernel) (by decide +kernel) (by decide +kernel) u v\n")


def class_block_multi(name, P, Q, F, M, phi, g0s, certs, B, V, L, label, nname):
    """A class with several norm representatives: one analytic certificate and one Matveev premise per
    representative (`matveev_{name}_j`), combined by `UnitPremises.analytic_cons`; the class premise
    `matveev_{name}` is their conjunction."""
    k = len(g0s)
    out = ''
    for j, (g0, cert) in enumerate(zip(g0s, certs)):
        nj = f'{name}_{j}'
        cases = cert['cases_json']
        check_cases(cases, B)
        assert len(cases) == 3 and cert['V'] == V
        out += ''.join(f"/-- Case {i} of {label}, representative {j}. -/\n"
                       f"def case_{nj}_{i} : UnitPremises.Case :=\n  {case_lean(c)}\n\n" for i, c in enumerate(cases))
        out += (f"/-- The analytic statement of {label} for the representative `{z3_lean(g0)}`. -/\n"
                f"def analytic_{nj} : Prop :=\n  UnitPremises.Analytic {form_lean(F)} {_i(M)} {P} {Q} {z3_lean(phi)} "
                f"e1 e1i e2 e2i {V} [({z3_lean(g0)}, [{', '.join(f'case_{nj}_{i}' for i in range(3))}])]\n\n")
        out += analytic_block(nj, P, Q, F, M, phi, g0, cert, V, f'{label}, representative {j}')
    reps = ', '.join(f"({z3_lean(g0)}, [{', '.join(f'case_{name}_{j}_{i}' for i in range(3))}])"
                     for j, g0 in enumerate(g0s))
    proj = [('hM' + '.2' * j + ('.1' if j < k - 1 else '')) for j in range(k)]
    proof = '(UnitPremises.analytic_nil _ _ _ _ _ _ _ _ _ _)'
    for j in reversed(range(k)):
        proof = f'(UnitPremises.analytic_cons (analytic_{name}_{j}_proved {proj[j]}) {proof})'
    out += (f"/-- The representatives of {label} with their analytic cases. -/\n"
            f"def reps_{name} : List (Z3 × List UnitPremises.Case) :=\n  [{reps}]\n\n"
            f"/-- **Matveev's lower bound for {label}**: one instance per representative.  Not proved in Lean. -/\n"
            f"def matveev_{name} : Prop := {' ∧ '.join(f'matveev_{name}_{j}' for j in range(k))}\n\n"
            f"/-- The analytic statement for {label} (all representatives). -/\n"
            f"def analytic_{name} : Prop :=\n  UnitPremises.Analytic {form_lean(F)} {_i(M)} {P} {Q} {z3_lean(phi)} "
            f"e1 e1i e2 e2i {V} reps_{name}\n\n"
            f"theorem analytic_{name}_proved (hM : matveev_{name}) : analytic_{name} :=\n  {proof}\n\n"
            f"/-- Negative control: every chain of {label} with its final bound lowered by one is rejected. -/\n"
            f"theorem forged_rejected_{name} : UnitPremises.forgedRejectedB reps_{name} = true := by decide +kernel\n\n")
    out += (f"/-- **{label}, complete under Matveev's bound** ({k} norm representatives): `{list(F)}` takes the "
            f"value {M} exactly at {len(L)} point(s). -/\n"
            f"theorem class_{name} (hM : matveev_{name}) (u v : ℤ) :\n"
            f"    evalF {form_lean(F)} u v = {_i(M)} ↔ (u, v) ∈ ({pairs_lean(L)} : List (ℤ × ℤ)) :=\n"
            f"  thue_list {form_lean(F)} {_i(M)} {P} {Q} {z3_lean(phi)} (reps_{name}.map Prod.fst) e1 e1i e2 e2i {B} {V} "
            f"{pairs_lean(L)}\n    (by decide) (by decide)\n"
            f"    (UnitPremises.extBound_of _ _ _ _ _ _ _ _ _ _ _ reps_{name} unitGen_proved ({nname}_proved)\n"
            f"      (fun a b => by simp only [UnitPremises.nrm, enc, evalF]; ring) (analytic_{name}_proved hM) "
            f"(by decide +kernel))\n"
            f"    (by decide +kernel) (by decide +kernel) (by decide +kernel) u v\n")
    return out


def box_hits(P, Q, F, M, phi, g0, e1, e1i, e2, e2i, B):
    hits = set()
    for g in fam(P, Q, g0, e1, e1i, e2, e2i, B):
        for h in (g, tuple(-x for x in g)):
            d = dec(F[0], phi, h)
            if enc(F[0], phi, *d) == h and evalF(F, *d) == M:
                hits.add(d)
    return hits


def head(name, doc):
    return (f"import PerfectPower.UnitGen\nimport PerfectPower.NormRepProof\nimport PerfectPower.AnalyticBridge\nimport PerfectPower.DescentThueList\n\n/-!\n{doc}\n-/\n\n"
            f"namespace PerfectPower.Generated.{name}\n\nopen PerfectPower ThueLocal UnitBox\n\n")


DOC756 = """# The field 756: seven Thue classes and three curves, under Matveev's bound
(generated by `python/make_lean_unit_fields.py`)

`K = ℚ(x)`, `x³ = 6x + 2`, `O_K = ℤ[x]`, discriminant 756.  Seven GL₂(ℤ)-classes of open branch
equations of `y² = x³ − D`, `D ∈ {7, 28, 63}`, live in this field (`MORDELL_BRANCH.md` §7.3).

* **Proved:** `unitGen_proved`, unit generation for `ℤ[x]` (`UnitGenProof.unitGen_of_cert`).
* **Proved:** `normRep_N_proved`, the norm representatives (`NormRepProof.normRep756`; classes 20
  and 50 share `normRep_64`).
* **Proved:** `analytic_i_proved`, the analytic statement of each class, from `matveev_i`
  (`AnalyticBridge.analytic_of_cert`; the interval certificate `acert_i` is checked by the kernel).
* **Premise, not proved in Lean:** one `matveev_i` per class, Matveev's lower bound for the three
  linear forms of the class (`AnalyticBridge.MatveevCase`).
* **Kernel-checked:** the direct-`H` reduction chains, the exponent boxes, the small-`b` searches,
  the norm identities, and the branch transport.
* `class_i`: the complete solution list.  `minusD`: the complete list of integral points of
  `y² = x³ − D`, under the Matveev premises of that curve's classes."""

DOC1944 = """# The order `ℤ[δ]`, `δ³ = 9δ + 6` (discriminant 1944): unit generation
(generated by `python/make_lean_unit_fields.py`)

Shared by every certificate in this order: the `D = 72` residual (`Generated/D72Unit.lean`) and
`y² = x³ − 18` (`Generated/Minus18.lean`) import it instead of re-checking the unit box.

* **Proved:** `unitGen_proved`, every unit of `ℤ[δ]` is `±ε₁^a ε₂^b`, `ε₁ = δ² − 3δ − 1`,
  `ε₂ = 2δ² − 1` (`UnitGenProof.unitGen_of_cert`, certificate checked by the kernel)."""

DOC72 = """# The `D = 72` residual `H(u, v) = −3u³ + 9uv² − 2v³ = ±1`, under Matveev's bound
(generated by `python/make_lean_unit_fields.py`)

`K = ℚ(δ)`, `δ³ = 9δ + 6`, `O_K = ℤ[δ]`, discriminant 1944.  The form `(−3, 0, 9, −2)` has
`φ = β = 6 − δ²` (`NormForm.d72_beta_of_delta`), and `N(c₀u − βv) = 9 H(u, v)`.

* **Proved:** `unitGen_proved`, unit generation for `ℤ[δ]` (imported from `Generated/Order1944.lean`).
* **Proved:** `normRep_pos_proved`, the norm representatives of norm 9 (`NormRepProof.normRep_d72`).
* **Proved:** `analytic_pos_proved`, from `matveev_pos` (`AnalyticBridge.analytic_of_cert`).
* **Premise, not proved in Lean:** `matveev_pos`, Matveev's lower bound for the three linear forms.
  The target `H = −1` uses the same facts, transported by sign (`UnitPremises.normRep_neg_of`,
  `analytic_neg_of`: the form, `enc` and the norm are odd).
* **Kernel-checked:** the reduction chains (`H ≤ 4`), the box of `9²` elements and the search
  `|v| ≤ 1`.  `class_pos`, `class_neg`: no solution."""


def main():
    f756 = json.loads((ROOT / 'receipts' / 'field756_bound.json').read_text())
    d72 = json.loads((ROOT / 'receipts' / 'd72_thue_bound.json').read_text())
    witness = json.loads((ROOT / 'receipts' / 'unit_basis_witness.json').read_text())
    local = json.loads((ROOT / 'receipts' / 'norm_rep_localization.json').read_text())
    graph = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
    gcls = {c['id']: c for c in graph['classes']}
    localized = {(f['P'], f['Q'], t['N']) for f in local['fields'] for t in t_iter(f)}
    report = {'fields': []}
    certs = []

    # ---- field 756
    P, Q = f756['P'], f756['Q']
    e1, e2 = (tuple(u) for u in f756['units'])
    pre, e1i, e2i, wrep = field_preamble(P, Q, e1, e2, witness)
    out = [head('Field756', DOC756), pre]
    lists, rows = {}, []
    shared = {}
    for c in f756['classes']:
        key = (c['form'][0] ** 2 * c['M'], tuple(c['gammas'][0]))
        shared.setdefault(key, []).append(c['class'])
    nnames = {}
    for (N, g0), ids in shared.items():
        nname = f"normRep_{N}" if sum(k[0] == N for k in shared) == 1 else f"normRep_{N}_{ids[0]}"
        for i in ids:
            nnames[i] = nname
        out.append(norm_rep_block(nname, P, Q, N, g0, [f'class {i}' for i in ids]))
    for c in f756['classes']:
        i, F, M, phi = c['class'], tuple(c['form']), c['M'], tuple(c['phi'])
        assert len(c['gammas']) == 1
        g0 = tuple(c['gammas'][0])
        cert = analytic_cert(P, Q, F, M, phi, g0, e1, e2, c['V0'])
        V, ccases = cert['V'], cert['cases_json']
        B = max(x['H_reduced'] for x in ccases)
        certs.append(_cert_json(f'field756 class {i}', cert))
        L = sorted(tuple(x) for x in c['pari_thue'])
        assert tuple(gcls[i]['representative']) == F and gcls[i]['M'] == M
        assert phi[1] != 0 or phi[2] != 0
        assert (P, Q, F[0] ** 2 * M) in localized
        hits = box_hits(P, Q, F, M, phi, g0, e1, e1i, e2, e2i, B)
        assert hits <= set(L), f'class {i}: box hit outside the list: {hits - set(L)}'
        assert {x for x in L if abs(x[1]) > V} <= hits, f'class {i}: positive control failed'
        sm = set(small_hits(F, M, V))
        assert sm <= set(L) and {x for x in L if abs(x[1]) <= V} <= sm
        lists[i] = L
        rows.append({'class': i, 'curves': c['curves'], 'B': B, 'V': V, 'box_size': (2 * B + 1) ** 2,
                     'box_hits': sorted(hits), 'small_b_hits': sorted(sm), 'list': L,
                     'reduction_steps': sum(len(x['steps']) for x in ccases), 'analytic': cert['report']})
        out.append(class_block(str(i), P, Q, F, M, phi, g0, ccases, B, V, L,
                               f"class {i} (`D ∈ {c['curves']}`, `M = {M}`)", nnames[i], cert=cert))
    census = {}
    with open(ROOT / 'data' / 'mordell_census.csv') as f:
        for row in csv.DictReader(f):
            census[int(row['k'])] = sorted(int(v) for v in row['x_coordinates'].split())
    curves = []
    for D in (7, 28, 63):
        c = compile_curve(D)
        a = lean_args(c)
        ids = next(x for x in graph['curves'] if x['D'] == D)['classes']
        thuesL, ys = [], set(a['Ys'])
        for e in c['open']:
            mem, cid = next((m, cid) for cid in ids for m in gcls[cid]['members']
                            if (m['D'], m['k'], m['p'], m['q']) == (D, e['k'], e['p'], e['q']))
            T = mem['T']
            thuesL.append(f"({_i(e['k'])}, {_i(e['p'])}, {_i(e['q'])}, {mat_lean(T)})")
            k3 = e['k'] ** 3
            for (u, v) in lists[cid]:
                aa, bb = T[0][0] * u + T[0][1] * v, T[1][0] * u + T[1][1] * v
                W = e['p'] * W1(D, aa, bb) + D * e['q'] * W2(D, aa, bb)
                if W % k3 == 0:
                    ys.add(W // k3)
        ys = sorted(ys)
        pts = [(icbrt(y * y + D), y) for y in ys if icbrt(y * y + D) ** 3 == y * y + D]
        assert sorted({x for x, _ in pts}) == census.get(-D, []), f'D = {D}: disagrees with the Sage census'
        curves.append({'D': D, 'classes': ids, 'open_branches': len(c['open']), 'points': pts,
                       'candidate_ys': ys, 'agrees_with_sage': True})
        cubes = '[' + ', '.join('(' + ', '.join(_i(v) for v in t) + ')' for t in a['cubes']) + ']'
        mods = '[' + ', '.join('(' + ', '.join(_i(v) for v in t) + ')' for t in a['mods']) + ']'
        listed = '[' + ', '.join(
            f"({form_lean(gcls[i]['representative'])}, {gcls[i]['M']}, {pairs_lean(lists[i])})" for i in ids) + ']'
        hyps = ' '.join(f'(hM{i} : matveev_{i})' for i in ids)
        pat = ' | '.join(['rfl'] * len(ids))
        cases = ' '.join(f'| exact (class_{i} hM{i} u v).mp' for i in ids)
        out.append(
            f"set_option maxHeartbeats 0 in\n"
            f"/-- **The integral points of `y^2 = x^3 - {D}`, under the Matveev premises of classes {ids}**: "
            f"{len(pts)} point(s).  {len(a['cubes'])} field-cube and {len(a['mods'])} local branches; "
            f"{len(thuesL)} branches transported to the listed classes. -/\n"
            f"theorem minus{D} {hyps}\n    (x y : ℤ) : y ^ 2 = x ^ 3 - {D} ↔ (x, y) ∈ ({pairs_lean(pts)} : List (ℤ × ℤ)) :=\n"
            f"  DescentThueList.complete_of_lists {D} (by norm_num) {c['r']} {c['t']} (by norm_num) (by norm_num)"
            f" {c['K']} {c['Q']}\n    (by norm_num) (by norm_num)\n"
            f"    {cubes}\n    {mods}\n    [] []\n    [{', '.join(thuesL)}]\n    {listed}\n"
            f"    (by simp)\n"
            f"    (by intro c hc u v; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc\n"
            f"        rcases hc with {pat} <;> first {cases})\n"
            f"    {'[' + ', '.join(_i(y) for y in ys) + ']'}\n"
            f"    {pairs_lean(pts)}\n    (by decide +kernel) (by decide +kernel) x y\n")
    out.append('end PerfectPower.Generated.Field756\n')
    (ROOT / 'PerfectPower' / 'Generated' / 'Field756.lean').write_text('\n'.join(out))
    report['fields'].append({'field': 'x^3 - 6x - 2', 'unit_witness': wrep, 'classes': rows, 'curves': curves})

    # ---- D = 72
    P, Q = d72['P'], d72['Q']
    e1, e2 = (tuple(u) for u in d72['units'])
    pre, e1i, e2i, wrep = field_preamble(P, Q, e1, e2, witness)
    # the order ℤ[δ] is shared (D = 72 and D = 18): its unit generation lives in its own module
    (ROOT / 'PerfectPower' / 'Generated' / 'Order1944.lean').write_text(
        "import PerfectPower.UnitGen\n\n/-!\n" + DOC1944 + "\n-/\n\n"
        "namespace PerfectPower.Generated.Order1944\n\nopen PerfectPower ThueLocal UnitBox\n\n"
        + pre + "\nend PerfectPower.Generated.Order1944\n")
    out = [head('D72Unit', DOC72).replace('import PerfectPower.UnitGen\n', 'import PerfectPower.Generated.Order1944\n')
           .replace('open PerfectPower ThueLocal UnitBox\n', 'open PerfectPower ThueLocal UnitBox Order1944\n')]
    F, phi, g0 = tuple(d72['form']), tuple(d72['phi']), tuple(d72['gammas'][0])
    cert = analytic_cert(P, Q, F, 1, phi, g0, e1, e2, d72['V0'])
    V, ccases = cert['V'], cert['cases_json']
    B = max(x['H_reduced'] for x in ccases)
    certs.append(_cert_json('D = 72, H = 1', cert))
    rows = []
    out.append(norm_rep_block('normRep_pos', P, Q, F[0] ** 2, g0, ['`H = 1` (and, transported by sign, `H = -1`)']))
    for name, M, g in (('pos', 1, g0), ('neg', -1, tuple(-x for x in g0))):
        assert (P, Q, F[0] ** 2 * M) in localized
        hits = box_hits(P, Q, F, M, phi, g, e1, e1i, e2, e2i, B)
        assert not hits and not small_hits(F, M, V)
        rows.append({'M': M, 'B': B, 'V': V, 'box_size': (2 * B + 1) ** 2, 'box_hits': [],
                     'reduction_steps': sum(len(x['steps']) for x in ccases), 'analytic': cert['report']})
        out.append(class_block(name, P, Q, F, M, phi, g, ccases, B, V, [], f'`H(u, v) = {M}`',
                               'normRep_pos', neg_of=None if M == 1 else 'pos', cert=cert))
    out.append('end PerfectPower.Generated.D72Unit\n')
    (ROOT / 'PerfectPower' / 'Generated' / 'D72Unit.lean').write_text('\n'.join(out))
    report['fields'].append({'field': 'x^3 - 9x - 6', 'unit_witness': wrep, 'classes': rows})

    (ROOT / 'receipts' / 'analytic_certificates.json').write_text(json.dumps(
        {'label': 'analytic certificates for AnalyticBridge.analytic_of_cert (exact replay of caseCompute/caseOK; '
                  'Matveev constants from exact rational height and log bounds)',
         'classes': certs}, indent=1) + '\n')
    report['label'] = ('Lean theorems conditional on the named Matveev premises matveev_i (unitGen, '
                       'normRep and analytic_i proved) '
                       '(Generated/Field756.lean, Generated/D72Unit.lean); reduction chains, norm identities, '
                       'boxes, small-b searches and branch transport are kernel-checked')
    (ROOT / 'receipts' / 'unit_fields_certificate.json').write_text(json.dumps(report, indent=1, default=list) + '\n')
    for f in report['fields']:
        print(f"{f['field']}: unit box {f['unit_witness']}")
        for r in f['classes']:
            print(f"  {r.get('class', r.get('M'))}: B={r['B']} V={r['V']} box {r['box_size']} "
                  f"steps {r['reduction_steps']} hits {r['box_hits']}")
        for c in f.get('curves', []):
            print(f"  D={c['D']}: classes {c['classes']}, points {c['points']}")


def t_iter(f):
    return f['targets']


if __name__ == '__main__':
    main()
