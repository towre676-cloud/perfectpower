"""Composable divisor covers and the norm-representative theorems built from them
(`PerfectPower/Generated/Covers<disc>.lean`, `receipts/norm_covers.json`).

For an order `ℤ[t]`, `t³ = Pt + Q`, a *cover* for `d` is a list of elements of norm `±d` that divides
every element whose norm `d` divides (`NormCover.coverB`, checked modulo `m`, `d ∣ m`).  The list of
representatives for `N = d₁ d₂ ⋯ d_k` is built one factor at a time: the products `γ t'` of a cover
element and a previous representative, with associates removed (`assocB`) and each kept element
replaced by a small associate (multiplication by `ε₁^i ε₂^j`; any associate is valid).  The Lean side
checks every step (`NormCover.normRepAbs_step'`).

The covers for `t³ = 15t + 20` (norm 4: `A, B, C` mod 4; norm 9: `η` mod 9) and the unit relation
`A C ε₂ = −B²` are from the shared-norm-cover review of `6a7bc79`; the relation is why the closure
for `4ʳ` stays at `2r + 1` elements.

Run: python3 python/norm_cover.py
"""
from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

import make_lean_unit_fields as U  # noqa: E402
from norm_rep_search import adj, divides  # noqa: E402

COVERS = {
    (15, 20): {'name': 'Covers2700', 'units': [(-1, 1, 1), (-59, -22, 8)],
               'covers': {4: (4, [(-4, -4, -1), (-6, -3, 1), (-11, -2, 1)]), 9: (9, [(-11, -1, 1)])},
               # each target as its chain of factors (applied left to right, starting from 1)
               'targets': {4: [4], 16: [4, 4], 64: [4, 4, 4], 4096: [4, 4, 4, 4, 4, 4], 9: [9], 36: [4, 9]}},
    # prime covers found with a candidate box of radius 25 (python/norm_rep_search.reps_of_norm)
    (27, 52): {'name': 'Covers5724', 'units': [(-5, -2, 0), (-253, -170, -28)],
               'covers': {2: (2, [(-3, -1, 0), (-6, 1, 0)]), 3: (3, [(-7, -2, 0)])},
               'targets': {36: [2, 2, 3, 3]}},
    (21, 32): {'name': 'Covers9396', 'units': [(-15, -1, 1), (-379, -322, -62)],
               'covers': {4: (4, [(-3, -1, 0), (-4, -4, -1), (-9, -5, 0), (-17, -2, 1)])},
               'targets': {4: [4]}},
    (15, 16): {'name': 'Covers6588', 'units': [(-5, -3, 1), (-40907, -47810, -11056)],
               'covers': {2: (2, [(-1, -1, 0), (-10, -2, 1)]), 3: (3, [(-9, -10, -2)])},
               'targets': {36: [2, 2, 3, 3]}},
    # t³ = 60t + 178 (disc 8532): a common overorder of the D = 79 orders (python/order_transport.EXTRA_TARGETS).
    # 7 = p₁p₂ with N(p₂) = 49, so there is no cover for 7; norm 49 is a residue certificate in Minus79
    (60, 178): {'name': 'Covers8532', 'units': [(-151, -19, 4), (-101, -45, -5)],
                'covers': {2: (2, [(-4, -1, 0)]), 3: (3, [(-5, -1, 0)])},
                'targets': {4: [2, 2], 9: [3, 3]}},
}


def cover_ok(P, Q, d, m, reps):
    """Exact mirror of `NormCover.coverB`."""
    if m <= 0 or m % d or not all(abs(U.nrm(P, Q, g)) == d for g in reps):
        return False
    return all(U.nrm(P, Q, r) % d or any(divides(P, Q, g, r) for g in reps)
               for r in itertools.product(range(m), repeat=3))


def assoc(P, Q, x, t):
    """Exact mirror of `NormCover.assocB`."""
    n = U.nrm(P, Q, t)
    y = U.mul(P, Q, x, adj(P, Q, t))
    return n != 0 and all(c % n == 0 for c in y) and abs(U.nrm(P, Q, x)) == abs(n)


def small_associate(P, Q, g, units, R=6):
    e1, e2 = units
    i1, i2 = U.inverse(P, Q, e1), U.inverse(P, Q, e2)
    best = g
    for i in range(-R, R + 1):
        for j in range(-R, R + 1):
            h = U.mul(P, Q, U.mul(P, Q, g, U._zp(P, Q, e1, i)), U._zp(P, Q, e2, j))
            if (max(map(abs, h)), sum(map(abs, h))) < (max(map(abs, best)), sum(map(abs, best))):
                best = h
    if U.nrm(P, Q, best) < 0:                 # norm exactly +N (−1 is a unit)
        best = tuple(-c for c in best)
    assert assoc(P, Q, best, g) and assoc(P, Q, g, best)
    return best


def closure(P, Q, reps, prev, units):
    out = []
    for g in reps:
        for t in prev:
            x = U.mul(P, Q, g, t)
            if not any(assoc(P, Q, x, s) for s in out):
                out.append(small_associate(P, Q, x, units))
    assert all(any(assoc(P, Q, U.mul(P, Q, g, t), s) for s in out) for g in reps for t in prev)
    return out


def build(P, Q):
    cfg = COVERS[(P, Q)]
    name = cfg['name']
    for d, (m, reps) in cfg['covers'].items():
        assert cover_ok(P, Q, d, m, reps), (d, m)
    lists = {1: [(1, 0, 0)]}
    steps = {}
    for N, chain in sorted(cfg['targets'].items()):
        prev_n, prev = 1, [(1, 0, 0)]
        for d in chain:
            n = prev_n * d
            if n not in lists:
                lists[n] = closure(P, Q, cfg['covers'][d][1], prev, cfg['units'])
                steps[n] = (d, prev_n)
            prev_n, prev = n, lists[n]
    z = U.z3_lean
    out = [f"import PerfectPower.NormCover\n\n/-!\n# Divisor covers and norm representatives in `ℤ[t]`, `t³ = {P}t + {Q}`\n"
           f"(generated by `python/norm_cover.py`)\n\n"
           f"Covers: " + '; '.join(f"norm `{d}` modulo `{m}` by {len(r)} element(s)" for d, (m, r) in cfg['covers'].items()) +
           f".  Each `rep_N` is built from them one factor at a time (`NormCover.normRepAbs_step'`); the\n"
           f"closure checks keep one small associate of every product.\n-/\n\n"
           f"namespace PerfectPower.Generated.{name}\n\nopen PerfectPower UnitBox NormCover\n"]
    for d, (m, reps) in cfg['covers'].items():
        out.append(f"/-- The cover for norm `{d}`, checked modulo `{m}`. -/\n"
                   f"def cov_{d} : List Z3 := [{', '.join(z(g) for g in reps)}]\n\n"
                   f"theorem cover_{d} : coverB {P} {Q} {d} {m} cov_{d} = true := by decide +kernel\n")
    for n in sorted(lists):
        if n == 1:
            continue
        d, pn = steps[n]
        prev = '[(1, 0, 0)]' if pn == 1 else f'L_{pn}'
        prev_thm = f'(normRepAbs_one {P} {Q})' if pn == 1 else f'rep_{pn}'
        out.append(f"/-- Representatives of norm `±{n}` ({len(lists[n])}). -/\n"
                   f"def L_{n} : List Z3 := [{', '.join(z(g) for g in lists[n])}]\n\n"
                   f"theorem rep_{n} : NormRepAbs {P} {Q} {n} L_{n} :=\n"
                   f"  normRepAbs_step' (by norm_num) (by norm_num) cover_{d} {prev_thm} (by decide +kernel)\n")
    out.append(f"end PerfectPower.Generated.{name}\n")
    (ROOT / 'PerfectPower' / 'Generated' / f'{name}.lean').write_text('\n'.join(out))
    return {'order': [P, Q], 'module': name,
            'covers': {str(d): {'modulus': m, 'reps': reps} for d, (m, reps) in cfg['covers'].items()},
            'lists': {str(n): L for n, L in sorted(lists.items())},
            'sizes': {str(n): len(L) for n, L in sorted(lists.items())}}


def main():
    rows = [build(P, Q) for (P, Q) in COVERS]
    (ROOT / 'receipts' / 'norm_covers.json').write_text(json.dumps(
        {'label': 'Divisor covers and composed norm representatives (Lean: Generated/Covers*.lean)',
         'orders': rows}, indent=1, default=list) + '\n')
    for r in rows:
        print(r['module'], r['sizes'])


if __name__ == '__main__':
    main()
