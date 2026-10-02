"""The blocker map for the 104 irreducible positive-k Thue equations (`receipts/rank_one_blockers.json`).

For each irreducible class of `receipts/positive_k_next.json` this script records what stands
between it and a Lean source theorem, using the exact mirrors of `python/rank_one_sources.py`:
* `lean_source`: certified in `Generated/RankOneSources/K{k}.lean` (`RankOne.source`);
* `ready_large_slab`: fundamental unit and Skolem prime found, but the slab check is large
  (its kernel cost is the obstacle);
* `several_solutions`: more than one known solution, so a list-valued source theorem is needed;
* `no_skolem_prime`: no odd prime `p ≤ 97` with period `M ≤ 200` satisfies the Skolem conditions
  for both `η` and `η⁻¹`;
* `no_unit_found`: no unit with `c < cmax` (a large regulator);
* `nonmonic`: leading coefficient `±2, ±3, ±4`, which needs norm representatives.
Monic sources are grouped by their order `ℤ[z]`, `z³ = Pz + Q` (up to `z ↦ −z`), so unit work can
be charged once per order.

This is a search, not a proof: every status other than `lean_source` is a lead.  It takes a few
minutes (the unit search for large regulators) and is not part of `make verify`.

Run: python3 python/rank_one_scan.py [cmax]
"""
from __future__ import annotations

import itertools
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

import rank_one_sources as R  # noqa: E402

LARGE_SLAB = 200_000


def small_unit(P, Q, t):
    for rad in (4, 8, 14, 22):
        cands = [g for g in itertools.product(range(-rad, rad + 1), repeat=3)
                 if g[1:] != (0, 0) and abs(R.nrm(P, Q, g)) == 1]
        if cands:
            return min(cands, key=lambda g: abs(math.log(abs(R.sig(t, g)))))
    return None


def slab_unit(P, Q, t, cmax):
    """A unit with a large `σ`: `j ≈ 0` and `re ≈ 0` force `b ≈ cρ`, `a ≈ bρ/2 − cP + cρ²/2`."""
    for c in range(1, cmax):
        for b in (math.floor(c * t), math.ceil(c * t)):
            ac = b * t / 2 - c * P + c * t * t / 2
            for a in range(math.floor(ac) - 1, math.ceil(ac) + 2):
                if abs(R.nrm(P, Q, (a, b, c))) == 1:
                    return (a, b, c)
    return None


def classify(e, certified, cmax):
    mo = e['monic_order']
    row = {'k': e['k'], 'form': e['form'], 'known_representations': e['known_representations']}
    if mo is None:
        row['status'] = 'nonmonic'
        row['leading'] = e['form'][0]
        return row
    P, Q, h = -mo['p'], -mo['q'], mo['u_shift']
    row.update({'P': P, 'Q': Q, 'h': h, 'order': [P, abs(Q)]})
    if (e['k'], tuple(e['form'])) in certified:
        row['status'] = 'lean_source'
        return row
    t = R.real_root(P, Q)
    start = small_unit(P, Q, t) or slab_unit(P, Q, t, cmax)
    if start is None:
        row['status'] = 'no_unit_found'
        row['cmax'] = cmax
        return row
    eta, c = R.fundamental(P, Q, start)
    eps = R.inverse(P, Q, eta)
    se, sx = R.skolem(P, Q, eta), R.skolem(P, Q, eps)
    row['eta'] = list(eta)
    row['slab_elements'] = sum(1 for _ in R.slab(P, c))
    row['skolem'] = se and sx and se[0] == sx[0] and {'p': se[0], 'M': se[1]}
    if len(e['known_representations']) > 1:
        row['status'] = 'several_solutions'
    elif not row['skolem']:
        row['status'] = 'no_skolem_prime'
    else:
        row['status'] = 'ready_large_slab' if row['slab_elements'] > LARGE_SLAB else 'ready'
    return row


def main(cmax=2_000_000):
    eqs = json.loads((ROOT / 'receipts' / 'positive_k_next.json').read_text())['equations']
    certified = {(k, tuple(F)) for k, F, *_ in R.TARGETS}
    rows = [classify(e, certified, cmax) for e in eqs]
    tally = {}
    for r in rows:
        tally[r['status']] = tally.get(r['status'], 0) + 1
    orders = {}
    for r in rows:
        if 'order' in r:
            orders.setdefault(tuple(r['order']), []).append(r['k'])
    shared = {f'{P},{Q}': ks for (P, Q), ks in sorted(orders.items()) if len(ks) > 1}
    out = {'scope': 'blockers for the irreducible positive-k sources; a search, not a proof (only lean_source is a theorem)',
           'large_slab_threshold': LARGE_SLAB, 'unit_search_cmax': cmax,
           'summary': {'sources': len(rows), 'by_status': dict(sorted(tally.items())),
                       'monic_orders': len(orders), 'orders_shared_by_several_sources': shared},
           'sources': rows}
    (ROOT / 'receipts' / 'rank_one_blockers.json').write_text(json.dumps(out, indent=1) + '\n')
    return out


if __name__ == '__main__':
    s = main(*(int(a) for a in sys.argv[1:]))['summary']
    print(json.dumps(s['by_status']), f"{s['monic_orders']} monic orders,",
          f"{len(s['orders_shared_by_several_sources'])} shared")
