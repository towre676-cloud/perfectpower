"""Certificates for `RankOne.source` (`PerfectPower/RankOne.lean`): monic rank-one Thue sources.

For a class `F = (−1, 0, −p, −q)` (standard coefficients) of `y² = x³ + k`, `F(u, v) = −N(u − vz)`
in `ℤ[z]`, `z³ = P z + Q` with `P = −p`, `Q = −q`.  This script finds, with exact arithmetic:
* `η`, the unit with `σ(η) > 1` that the box check certifies as fundamental (`RankOne.boxB`);
  the search starts from the bounded p = 3 candidate of the second OEIS handoff and walks down to
  any smaller unit the box exposes;
* the rational bracket of the real root, `J ≥ 1/κ`, and the box `A, B, C` (`RankOne.condB`);
* an odd prime `p` and an exponent `M` with `Mx(η)^M = 1 + pD`, `p ∤ D₂₀`, `p ∤ (Mx(η)^r)₂₀` for
  `0 < r < M`, and the same for `ε = η⁻¹` (`RankOne.SkolemData`).
Every condition is re-checked by the Lean kernel; this script only searches.

Run: python3 python/rank_one_sources.py   (writes receipts/rank_one_sources.json and
`PerfectPower/Generated/RankOneSources.lean`)
"""
from __future__ import annotations

import json
import math
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# (k, P, Q, start unit from the handoff scan)
TARGETS = [(4, 0, -4, (1, -1, -1)), (33, -6, -10, (3, 1, -1)), (49, 0, -14, (1, -2, -1)),
           (81, 0, -18, (1, 3, 1))]


def mul(P, Q, x, y):
    """Mirror of `UnitBox.mul`."""
    a, b, c = x
    d, e, f = y
    c0, c1, c2, c3, c4 = a * d, a * e + b * d, a * f + b * e + c * d, b * f + c * e, c * f
    return (c0 + Q * c3, c1 + P * c3 + Q * c4, c2 + P * c4)


def nrm(P, Q, g):
    """Mirror of `UnitPremises.nrm`."""
    a, b, c = g
    return (a * ((a + P * c) * (a + P * c) - (P * b + Q * c) * b)
            - Q * c * (b * (a + P * c) - (P * b + Q * c) * c)
            + Q * b * (b * b - (a + P * c) * c))


def Mx(P, Q, g):
    cols = [mul(P, Q, g, e) for e in ((1, 0, 0), (0, 1, 0), (0, 0, 1))]
    return [[cols[j][i] for j in range(3)] for i in range(3)]


def mm(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(3)) for j in range(3)] for i in range(3)]


def neg(g):
    return tuple(-x for x in g)


def real_root(P, Q):
    f = lambda x: x ** 3 - P * x - Q                         # noqa: E731
    lo, hi = -100.0, 100.0
    for _ in range(200):
        m = (lo + hi) / 2
        if (f(lo) < 0) == (f(m) < 0):
            lo = m
        else:
            hi = m
    return lo


def sig(t, g):
    return g[0] + g[1] * t + g[2] * t * t


def inverse(P, Q, g):
    """`g⁻¹` for a unit of norm 1: solve `Mx g · x = e₀` (adjugate, det = 1)."""
    A = Mx(P, Q, g)
    det = (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1]) - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
           + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0]))
    assert det == 1
    # first column of the adjugate
    x = (A[1][1] * A[2][2] - A[1][2] * A[2][1], -(A[1][0] * A[2][2] - A[1][2] * A[2][0]),
         A[1][0] * A[2][1] - A[1][1] * A[2][0])
    assert mul(P, Q, g, x) == (1, 0, 0)
    return x


def normalize(P, Q, t, g):
    """The unit `±g^{±1}` with `σ > 1` (hence norm 1)."""
    if sig(t, g) < 0:
        g = neg(g)
    assert nrm(P, Q, g) == 1
    if sig(t, g) < 1:
        g = inverse(P, Q, g)
    assert sig(t, g) > 1
    return g


# ----- exact mirrors of RankOne.Cert / condB / boxB --------------------------------------------

def sigQ(x, g):
    return g[0] + g[1] * x + g[2] * x * x


def rad(g, lo, hi):
    return (hi - lo) * (abs(Fr(g[1])) + 2 * abs(Fr(g[2])) * max(abs(lo), abs(hi)))


def pHi(g, lo, hi):
    return abs(sigQ(lo, g)) + rad(g, lo, hi)


def cert(P, Q, eta, den=10 ** 9):
    t = real_root(P, Q)
    lo, hi = Fr(math.floor(t * den), den), Fr(math.ceil(t * den), den)
    cub = lambda x: x ** 3 - P * x - Q                       # noqa: E731
    assert lo < hi and cub(lo) * cub(hi) < 0
    T = max(abs(lo), abs(hi))
    t2lo = lo * lo if lo >= 0 else hi * hi if hi <= 0 else Fr(0)
    K = 3 * t2lo / 4 - P
    Dn = 3 * t2lo - P
    assert K > 0 and Dn > 0
    J = Fr(math.ceil(math.sqrt(1 / float(K)) * 10 ** 6 + 1), 10 ** 6)
    assert K * J * J >= 1
    E = sigQ(lo, eta) + rad(eta, lo, hi)
    assert sigQ(lo, eta) - rad(eta, lo, hi) > 1
    C = math.floor((E + 1 + Fr(3, 2) * T * J) / Dn)
    c = {'lo': lo, 'hi': hi, 'J': J, 'C': C}
    assert E + 1 + Fr(3, 2) * T * J < (C + 1) * Dn
    c['_T'], c['_t2lo'] = T, t2lo
    return c


def lmin(x, lo, hi):
    return x * lo if x >= 0 else x * hi


def lmax(x, lo, hi):
    return x * hi if x >= 0 else x * lo


def ints(l, h):
    """Mirror of `RankOne.ints`."""
    return list(range(math.ceil(l), math.floor(h) + 1))


def slab(P, c):
    """Mirror of the enumeration of `RankOne.slabB`."""
    lo, hi, J, T, t2lo = c['lo'], c['hi'], c['J'], c['_T'], c['_t2lo']
    for cc in range(-c['C'], c['C'] + 1):
        for b in ints(lmin(Fr(cc), lo, hi) - J, lmax(Fr(cc), lo, hi) + J):
            for a in ints(-1 + lmin(Fr(b), lo, hi) / 2 - cc * P + lmin(Fr(cc), t2lo, T * T) / 2,
                          1 + lmax(Fr(b), lo, hi) / 2 - cc * P + lmax(Fr(cc), t2lo, T * T) / 2):
                yield (a, b, cc)


def box_failures(P, Q, eta, c):
    """Elements that make `slabB` false (a smaller unit, or a loose enclosure)."""
    bad = []
    allowed = {(1, 0, 0), (-1, 0, 0), tuple(eta), neg(eta)}
    for g in slab(P, c):
        if abs(nrm(P, Q, g)) != 1 or g in allowed:
            continue
        if pHi(g, c['lo'], c['hi']) >= 1:
            bad.append(g)
    return bad


def fundamental(P, Q, start):
    t = real_root(P, Q)
    eta = normalize(P, Q, t, start)
    while True:
        c = cert(P, Q, eta)
        bad = box_failures(P, Q, eta, c)
        if not bad:
            return eta, c
        smaller = [g for g in bad if 1 < abs(sig(t, g)) < sig(t, eta) - 1e-9]
        assert smaller, f'loose enclosure only: {bad[:3]}'
        eta = normalize(P, Q, t, min(smaller, key=lambda g: abs(sig(t, g))))


def skolem(P, Q, g, primes=(3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47), Mmax=60):
    """`(p, M, D)` with `Mx(g)^M = 1 + pD`, `p ∤ D₂₀`, `p ∤ (Mx(g)^r)₂₀` for `0 < r < M`."""
    A = Mx(P, Q, g)
    for p in primes:
        X = A
        for M in range(1, Mmax + 1):
            if all((X[i][j] - (i == j)) % p == 0 for i in range(3) for j in range(3)):
                D = [[(X[i][j] - (i == j)) // p for j in range(3)] for i in range(3)]
                ok = D[2][0] % p != 0
                Y = A
                for _ in range(1, M):
                    ok = ok and Y[2][0] % p != 0
                    Y = mm(Y, A)
                if ok:
                    return p, M, D
                break
            X = mm(X, A)
    return None


def find(k, P, Q, start):
    eta, c = fundamental(P, Q, start)
    eps = inverse(P, Q, eta)
    se, sx = skolem(P, Q, eta), skolem(P, Q, eps)
    return {'k': k, 'P': P, 'Q': Q, 'start': list(start), 'eta': list(eta), 'eps': list(eps),
            'cert': {x: str(v) for x, v in c.items() if not x.startswith('_')},
            'slab_elements': sum(1 for _ in slab(P, c)),
            'skolem_eta': se and {'p': se[0], 'M': se[1], 'D': se[2]},
            'skolem_eps': sx and {'p': sx[0], 'M': sx[1], 'D': sx[2]},
            'eta_from_start': tuple(eta) == normalize(P, Q, real_root(P, Q), start),
            '_c': c}


def _i(n):
    return f'({n})' if n < 0 else str(n)


def _z3(g):
    return '(' + ', '.join(_i(x) for x in g) + ')'


def _q(x):
    x = Fr(x)
    return f'({x.numerator} / {x.denominator} : ℚ)' if x.denominator != 1 else f'({x.numerator} : ℚ)'


def _mat(D):
    return '!![' + '; '.join(', '.join(_i(x) for x in row) for row in D) + ']'


def lean_block(r):
    k, P, Q, c = r['k'], r['P'], r['Q'], r['_c']
    se, sx = r['skolem_eta'], r['skolem_eps']
    PQ = f'{_i(P)} {_i(Q)}'
    out = [f"/-! ### `k = {k}`: `−u³ + ({P}) u v² + ({Q}) v³ = 1`, `z³ = {P} z + {Q}` -/\n",
           f"/-- The unit `η` with `σ(η) > 1` for `k = {k}`. -/\ndef η{k} : Z3 := {_z3(r['eta'])}\n",
           f"/-- `ε = η⁻¹` for `k = {k}`. -/\ndef ε{k} : Z3 := {_z3(r['eps'])}\n",
           f"/-- The rank-one certificate for `k = {k}`. -/\n"
           f"def c{k} : Cert := ⟨{_q(c['lo'])}, {_q(c['hi'])}, {_q(c['J'])}, {c['C']}⟩\n",
           f"theorem h1_{k} : mul {PQ} η{k} ε{k} = (1, 0, 0) := by decide\n",
           f"theorem h2_{k} : mul {PQ} ε{k} η{k} = (1, 0, 0) := by decide\n",
           f"theorem n1_{k} : nrm {PQ} η{k} = 1 := by decide\n",
           f"theorem n2_{k} : nrm {PQ} ε{k} = 1 := by decide\n",
           f"theorem cond_{k} : condB {PQ} η{k} c{k} = true := by decide +kernel\n"]
    out.append(f"theorem slab_{k} : slabB {PQ} η{k} c{k} = true := by decide +kernel\n")
    for nm, g, sk in (('η', 'η', se), ('ε', 'ε', sx)):
        out.append(f"theorem sk{nm}_{k} : SkolemData {sk['p']} {sk['M']} (Mx {PQ} {g}{k}) {_mat(sk['D'])} :=\n"
                   f"  ⟨by norm_num, by ext i j; fin_cases i <;> fin_cases j <;> decide, by decide,\n"
                   f"    by intro r h0 hr; interval_cases r <;> decide⟩\n")
    assert se['p'] == sx['p']
    out.append(f"/-- **The source theorem for `k = {k}`**: `−u³ + ({P}) u v² + ({Q}) v³ = 1 ↔ (u, v) = (−1, 0)`. -/\n"
               f"theorem source{k} (u v : ℤ) : -u ^ 3 + {_i(P)} * u * v ^ 2 + {_i(Q)} * v ^ 3 = 1 ↔ (u = -1 ∧ v = 0) :=\n"
               f"  source h1_{k} h2_{k} n1_{k} n2_{k} cond_{k} slab_{k} (p := {se['p']}) (by norm_num) skη_{k} skε_{k} u v\n")
    return '\n'.join(out)


HEAD = """import PerfectPower.RankOne

/-!
# Rank-one monic sources, certified (generated by `python/rank_one_sources.py`)

Each block proves `−u³ + P u v² + Q v³ = 1 ↔ (u, v) = (−1, 0)` with `RankOne.source`.
- **Units.** Unit generation in `ℤ[z]`, `z³ = P z + Q`, comes from a kernel-checked certificate
  (`condB`) and a slab check (`slabB`).
- **Zero set.** The `z²` coordinate of `ηⁿ` vanishes only at `n = 0`, by
  `SkolemP.corner_zero` at the prime given.

The starting units are the bounded `p = 3` candidates of the second OEIS handoff
(`receipts/skolem3_candidates.json`). The box shows that `η = ε⁻¹` generates the units.
-/

namespace PerfectPower.Generated.RankOneSources

open PerfectPower UnitBox UnitPremises RankOne

"""


def main(ks=None):
    rows, blocks = [], []
    for k, P, Q, s in TARGETS:
        if ks and k not in ks:
            continue
        r = find(k, P, Q, s)
        assert r['skolem_eta'] and r['skolem_eps']
        blocks.append(lean_block(r))
        r.pop('_c')
        rows.append(r)
    text = HEAD + '\n'.join(blocks) + '\nend PerfectPower.Generated.RankOneSources\n'
    (ROOT / 'PerfectPower' / 'Generated' / 'RankOneSources.lean').write_text(text)
    (ROOT / 'receipts' / 'rank_one_sources.json').write_text(json.dumps(
        {'scope': 'search for RankOne.source certificates; every condition is re-checked by the Lean kernel',
         'sources': rows}, indent=1) + '\n')
    return rows


if __name__ == '__main__':
    import sys
    for r in main([int(a) for a in sys.argv[1:]] or None):
        print(r['k'], r['eta'], r['cert']['C'], r['slab_elements'],
              r['skolem_eta']['p'], r['skolem_eta']['M'])
