"""Per-stage status of the 104 irreducible positive-k sources (`receipts/source_stages.json`).

The blocker ledger (`rank_one_blockers.json`) gives one status per source, which can hide progress:
a nonmonic source may already be normalized and stall only at its unit.  This file records each
stage separately, from the existing receipts (no new search):
* `normalization`: `monic`, `witness` (`python/witness_monic.py`), or `none` (nonmonic, no point);
* `unit`: `found` (with the slab size) or `not_found`;
* `zero_set`: `skolem` (one solution, `RankOne.source`), `finite_list` (`RankOneZeros.source_list`),
  `orbit_congruence` (no solution, `RankOneNorm.no_corner_zero` after the monic reduction),
  `none_found`, or `not_reached`;
* `lean`: whether a Lean source theorem exists (`Generated/RankOneSources`, `RankOneZeros`, `Plus2`).
Only `lean = true` is a theorem.

Run: python3 python/source_stages.py
"""
from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

import rank_one_sources as R  # noqa: E402
import rank_one_zeros as RZ  # noqa: E402


def main():
    led = json.loads((ROOT / 'receipts' / 'rank_one_blockers.json').read_text())['sources']
    wit = {(r['k'], tuple(r['form'])): r for r in json.loads((ROOT / 'receipts' / 'witness_monic.json').read_text())['sources']}
    zer = {(r['k'], tuple(r['form'])): r for r in json.loads((ROOT / 'receipts' / 'rank_one_zeros.json').read_text())['sources']}
    lean1 = {(k, tuple(F)) for k, F, *_ in R.TARGETS} | {(2, (-1, 0, -3, -2))}
    leanz = {(k, tuple(F)) for k, F, *_ in RZ.TARGETS if zer.get((k, tuple(F)), {}).get('status') == 'ok'}
    nf = ROOT / 'receipts' / 'rank_one_norm.json'
    leann = {(r['k'], tuple(r['form'])) for r in json.loads(nf.read_text())['sources'] if r['status'] == 'empty'} if nf.exists() else set()
    rows = []
    for r in led:
        key = (r['k'], tuple(r['form']))
        w = wit.get(key)
        row = {'k': r['k'], 'form': r['form'], 'known_representations': r['known_representations']}
        if r.get('witness_normalized') or (w and w['status'] != 'no_witness'):
            row['normalization'] = 'witness'
            src = w
        elif 'P' in r or key in lean1 or key in leanz:
            row['normalization'] = 'monic'
            src = r
        else:
            row['normalization'] = 'none'
            src = None
        st = src['status'] if src else 'no_witness'
        if key in leann:
            row['normalization'] = 'monic_reduction'
            row['unit'] = 'found'
            row['zero_set'] = 'orbit_congruence'
            row['lean'] = True
        elif key in lean1 or key in leanz:
            row['unit'] = 'found'
            row['zero_set'] = 'finite_list' if key in leanz else 'skolem'
            row['lean'] = True
        else:
            row['lean'] = False
            if src is None:
                row['unit'] = row['zero_set'] = 'not_reached'
            elif st == 'no_unit_found':
                row['unit'], row['zero_set'] = 'not_found', 'not_reached'
            else:
                row['unit'] = 'found'
                row['zero_set'] = 'none_found' if st == 'no_skolem_prime' else 'found'
                row['slab_elements'] = src.get('slab_elements')
                if st == 'ready_large_slab':
                    row['large_slab'] = True
        if not row['lean']:
            if row['normalization'] == 'none':
                row['blocker'] = 'normalization (nonmonic, no known point)'
            elif row['unit'] != 'found':
                row['blocker'] = 'unit not found'
            elif row['zero_set'] == 'none_found':
                row['blocker'] = 'no Skolem prime'
            elif row.get('large_slab'):
                row['blocker'] = 'large slab check'
            else:
                row['blocker'] = 'not compiled (another class of the curve is open)'
        rows.append(row)
    summ = {stage: dict(Counter(r[stage] for r in rows)) for stage in ('normalization', 'unit', 'zero_set', 'lean')}
    summ['blocker'] = dict(Counter(r.get('blocker', 'none (theorem)') for r in rows))
    out = {'scope': 'per-stage status of the irreducible positive-k sources, from existing receipts; only lean = true is a theorem',
           'summary': summ, 'sources': rows}
    (ROOT / 'receipts' / 'source_stages.json').write_text(json.dumps(out, indent=1, default=str) + '\n')
    return out


if __name__ == '__main__':
    print(json.dumps(main()['summary'], indent=1, default=str))
