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

# (k, standard form F = (−1, B, C, d), P, Q, shift h, η).  F(u, v) = −N((u + hv) − vz) in ℤ[z],
# z³ = Pz + Q.  The units η were found offline (`python/rank_one_scan.py`); here the slab check
# re-derives that η is fundamental, and the Lean kernel re-checks everything.
TARGETS = [
    (4, (-1, 0, 0, -4), 0, -4, 0, (5, -3, 2)),
    (33, (-1, 0, -6, -10), -6, -10, 0, (77, -13, 10)),
    (49, (-1, 0, 0, -14), 0, -14, 0, (29, -12, 5)),
    (81, (-1, 0, 0, -18), 0, -18, 0, (55, -21, 8)),
    (3, (-1, -3, 0, -2), 3, -4, 1, (9, -11, 5)),
    (10, (-1, 0, -3, -6), -3, -6, 0, (11521, -3185, 2473)),
    (25, (-1, 0, 0, -10), 0, -10, 0, (181, -84, 39)),
    (41, (-1, -3, 3, -9), 6, -14, 1, (1201, -888, 276)),
    (43, (-1, 0, -9, -8), -9, -8, 0, (308121, -26292, 31822)),
    (44, (-1, -6, 3, -4), 15, -26, 2, (1731, -1379, 303)),
    (44, (-1, 0, -6, -12), -6, -12, 0, (9337, -1682, 1144)),
    (48, (-1, 0, 3, -14), 3, -14, 0, (779, -443, 157)),
    (54, (-1, -3, 6, -10), 9, -18, 1, (121, -93, 25)),
    (57, (-1, -9, -6, -4), 21, -40, 3, (1109, -790, 148)),
    (57, (-1, -6, 0, -6), 12, -22, 2, (5, -4, 1)),
    (57, (-1, 0, -6, -14), -6, -14, 0, (69, -13, 8)),
    (82, (-1, 0, -3, -18), -3, -18, 0, (9577, -2675, 1193)),
    (98, (-1, -9, -6, -6), 21, -42, 3, (4201, -2883, 537)),
]
PRIMES = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97)


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


def skolem(P, Q, g, primes=PRIMES, Mmax=200):
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


def find(k, F, P, Q, h, start):
    eta, c = fundamental(P, Q, start)
    assert tuple(eta) == tuple(start), (k, eta, start)
    eps = inverse(P, Q, eta)
    se, sx = skolem(P, Q, eta), skolem(P, Q, eps)
    assert se and sx and se[0] == sx[0], k
    # F(u, v) = −(u + hv)³ + P (u + hv) v² + Q v³
    a, B, C, d = F
    assert (a, B, C, d) == (-1, -3 * h, -3 * h * h + P, -h ** 3 + P * h + Q), (k, F)
    return {'k': k, 'form': list(F), 'P': P, 'Q': Q, 'h': h, 'eta': list(eta), 'eps': list(eps),
            'cert': {x: str(v) for x, v in c.items() if not x.startswith('_')},
            'slab_elements': sum(1 for _ in slab(P, c)),
            'skolem_eta': {'p': se[0], 'M': se[1], 'D': se[2]},
            'skolem_eps': {'p': sx[0], 'M': sx[1], 'D': sx[2]},
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


def lean_block(r, i, chunk=4000):
    P, Q, c = r['P'], r['Q'], r['_c']
    se, sx = r['skolem_eta'], r['skolem_eps']
    PQ = f'{_i(P)} {_i(Q)}'
    n_c = 2 * c['C'] + 1
    per = max(1, r['slab_elements'] // n_c)
    w = max(1, min(n_c, chunk // per))
    n = -(-n_c // w)
    out = [f"/-! ### Source {i}: `F = {tuple(r['form'])}`, `z³ = ({P}) z + ({Q})`, shift `h = {r['h']}` -/\n",
           f"/-- The fundamental unit `η` (`σ(η) > 1`) of source {i}. -/\ndef η{i} : Z3 := {_z3(r['eta'])}\n",
           f"/-- `ε = η⁻¹` for source {i}. -/\ndef ε{i} : Z3 := {_z3(r['eps'])}\n",
           f"/-- The rank-one certificate for source {i}. -/\n"
           f"def c{i} : Cert := ⟨{_q(c['lo'])}, {_q(c['hi'])}, {_q(c['J'])}, {c['C']}⟩\n",
           f"theorem h1_{i} : mul {PQ} η{i} ε{i} = (1, 0, 0) := by decide\n",
           f"theorem h2_{i} : mul {PQ} ε{i} η{i} = (1, 0, 0) := by decide\n",
           f"theorem n1_{i} : nrm {PQ} η{i} = 1 := by decide\n",
           f"theorem n2_{i} : nrm {PQ} ε{i} = 1 := by decide\n",
           f"theorem cond_{i} : condB {PQ} η{i} c{i} = true := by decide +kernel\n"]
    if n == 1:
        out.append(f"theorem slab_{i} : slabB {PQ} η{i} c{i} = true := by decide +kernel\n")
    else:
        for m in range(n):
            out.append(f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
                       f"theorem chunk{i}_{m} : (List.range' ({m} * {w}) {w}).all (slabSliceB {PQ} η{i} c{i}) = true := "
                       f"by decide +kernel\n")
        out.append(f"theorem slab_{i} : slabB {PQ} η{i} c{i} = true :=\n"
                   f"  slabB_of_chunks (w := {w}) (n := {n}) (by decide) fun m hm => by\n"
                   f"    interval_cases m\n    exacts [{', '.join(f'chunk{i}_{m}' for m in range(n))}]\n")
    for nm, sk in (('η', se), ('ε', sx)):
        out.append(f"theorem sk{nm}_{i} : skolemB {PQ} {nm}{i} {sk['p']} {sk['M']} = true := by decide +kernel\n")
    out.append(f"/-- **Source {i}**: `−u³ + ({P}) u v² + ({Q}) v³ = 1 ↔ (u, v) = (−1, 0)`. -/\n"
               f"theorem source{i} (u v : ℤ) : -u ^ 3 + {_i(P)} * u * v ^ 2 + {_i(Q)} * v ^ 3 = 1 ↔ (u = -1 ∧ v = 0) :=\n"
               f"  haveI : Fact (Nat.Prime {se['p']}) := ⟨by norm_num⟩\n"
               f"  source h1_{i} h2_{i} n1_{i} n2_{i} cond_{i} slab_{i} (p := {se['p']}) (by norm_num) skη_{i} skε_{i} u v\n")
    return '\n'.join(out)


HEAD = """import PerfectPower.RankOne

/-!
# Rank-one monic sources for `k = {k}`, certified (generated by `python/rank_one_sources.py`)

Each source `F(u, v) = −N((u + hv) − vz)` in `ℤ[z]`, `z³ = Pz + Q`, gets
`−u³ + P u v² + Q v³ = 1 ↔ (u, v) = (−1, 0)` from `RankOne.source`. Applied at `u + hv`, this is
the source theorem for `F`.
- **Units.** Unit generation comes from a kernel-checked certificate (`condB`) and a slab check
  (`slabB`, in chunks when large). The slab check also shows that `η` is fundamental.
- **Zero set.** The `z²` coordinate of `ηⁿ` vanishes only at `n = 0`, by
  `SkolemP.corner_zero` at the prime given.
-/

set_option Elab.async false

namespace PerfectPower.Generated.RankOneSources.K{k}

open PerfectPower UnitBox UnitPremises RankOne

"""


def main(ks=None):
    rows = []
    by_k = {}
    for t in TARGETS:
        if ks and t[0] not in ks:
            continue
        by_k.setdefault(t[0], []).append(t)
    d = ROOT / 'PerfectPower' / 'Generated' / 'RankOneSources'
    d.mkdir(exist_ok=True)
    for k, ts in by_k.items():
        blocks = []
        for i, (k_, F, P, Q, h, eta) in enumerate(ts):
            r = find(k, F, P, Q, h, eta)
            blocks.append(lean_block(r, i))
            r.pop('_c')
            r['index'] = i
            rows.append(r)
        text = HEAD.replace('{k}', str(k)) + '\n'.join(blocks) + f'\nend PerfectPower.Generated.RankOneSources.K{k}\n'
        (d / f'K{k}.lean').write_text(text)
    if not ks:
        (ROOT / 'receipts' / 'rank_one_sources.json').write_text(json.dumps(
            {'scope': 'RankOne.source certificates; every condition is re-checked by the Lean kernel',
             'sources': rows}, indent=1) + '\n')
    return rows


if __name__ == '__main__':
    import sys
    for r in main([int(a) for a in sys.argv[1:]] or None):
        print(r['k'], r['index'], r['eta'], r['cert']['C'], r['slab_elements'],
              r['skolem_eta']['p'], r['skolem_eta']['M'])
