"""Why the descent certificate fails, over every unresolved Mordell curve y^2 = x^3 + k, |k| <= 100.

For k < 0 (D = -k), `descent.diagnose(D)` names the first failing checks of the certificate
(`Descent.lean`): search limits (`BOX`), a norm-1 representation the table rejects because it
assumes the units are +-1 (`UNIT_BEYOND_PM1`; only D = 1, where every unit is a cube), a representation that is
an element cube (`ELEMENT_CUBE`), a cube only in the maximal order (`NONMAXIMAL_CUBE`), residue
checks failing because Z[sqrt(-D)] is not integrally closed (`NONMAXIMAL`), a representation that
is not a cube with 3 | h(Q(sqrt(-D))) (`CLASS_3`), or not a cube with 3 not dividing h
(`NOT_COPRIME`).  For k > 0 the factorization lives in a real quadratic field with infinitely
many units; this certificate does not apply (`REAL_QUADRATIC`).

A *repair* is a change of the certificate that removes one or more categories.  The receipt
counts, for each repair, the curves whose every failure it removes: the curves it would unlock,
if the repaired certificate were formalized.  Nothing here is a proof.

Writes receipts/mordell_obstructions.json.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.descent import diagnose  # noqa: E402
from perfectpower.oeis import unresolved_mordell  # noqa: E402

REPAIRS = {
    'absorb cube units (Z[i]: all units are cubes)': {'UNIT_BEYOND_PM1'},
    'accept element cubes in the table': {'ELEMENT_CUBE'},
    'cube units + element cubes': {'UNIT_BEYOND_PM1', 'ELEMENT_CUBE'},
    'descent in the maximal order': {'NONMAXIMAL', 'NONMAXIMAL_CUBE'},
    'maximal order + element cubes': {'NONMAXIMAL', 'NONMAXIMAL_CUBE', 'ELEMENT_CUBE'},
    'coprimality at 2 and at D (case split on the gcd)': {'NOT_COPRIME'},
    'maximal order + element cubes + coprimality': {'NONMAXIMAL', 'NONMAXIMAL_CUBE', 'ELEMENT_CUBE',
                                                    'NOT_COPRIME'},
}


def main():
    rows = []
    for cv in unresolved_mordell(-100, 100):
        k = cv['k']
        if k > 0:
            rows.append({'k': k, 'categories': ['REAL_QUADRATIC'], 'x_found_by_scan': cv['x_found_by_scan']})
        else:
            rows.append({'k': k, **diagnose(-k), 'x_found_by_scan': cv['x_found_by_scan']})
    # the expert_push bounded scan (all 200 curves, x <= 100000), joined by k; its counts are kept
    # separate: signed points, points with y >= 0, and distinct x
    ext = ROOT / 'expert_push' / 'receipts' / 'mordell_scan.json'
    published = {}
    atl = ROOT / 'receipts' / 'oeis_sqrt2_atlas.json'
    if atl.exists():
        m = json.loads(atl.read_text())['mordell']
        published = {r['k']: r['published_count'] for r in m['leads']}
    join = None
    if ext.exists():
        scan = {c['k']: c for c in json.loads(ext.read_text())['curves']}
        for r in rows:
            c = scan.get(r['k'])
            if c is None:
                continue
            pts = c['points']
            r['expert_scan'] = {'x_interval': c['x_interval'], 'signed_points': len(pts),
                                'nonnegative_y_points': sum(1 for _, y in pts if y >= 0),
                                'distinct_x': len({x for x, _ in pts}),
                                'published_signed_count': published.get(r['k'])}
        joined = [r for r in rows if 'expert_scan' in r]
        join = {'source': 'expert_push/receipts/mordell_scan.json (bounded search, x <= 100000)',
                'curves_joined': len(joined),
                'nonempty_in_scan': sum(r['expert_scan']['signed_points'] > 0 for r in joined),
                'signed_points_match_published': sum(r['expert_scan']['signed_points'] ==
                                                     r['expert_scan']['published_signed_count']
                                                     for r in joined),
                'with_published_count': sum(r['expert_scan']['published_signed_count'] is not None
                                            for r in joined),
                'note': 'the package scans all 200 nonsingular curves (103 nonempty); only the 155 '
                        'unresolved ones are joined here. A bounded scan proves membership, not completeness.'}
    tally = {}
    for r in rows:
        for c in r['categories']:
            tally[c] = tally.get(c, 0) + 1
    combos = {}
    for r in rows:
        key = '+'.join(r['categories'])
        combos[key] = combos.get(key, 0) + 1
    repairs = {name: sorted(r['k'] for r in rows if set(r['categories']) <= cats)
               for name, cats in REPAIRS.items()}
    out = {'curves': len(rows), 'negative_k': sum(r['k'] < 0 for r in rows),
           'category_counts': dict(sorted(tally.items())),
           'category_combinations': dict(sorted(combos.items(), key=lambda x: -x[1])),
           'repairs_unlock': {n: {'count': len(v), 'k': v} for n, v in repairs.items()},
           'y2_x3_minus_1': next(r for r in rows if r['k'] == -1),
           'expert_scan_join': join,
           'rows': rows}
    path = ROOT / 'receipts' / 'mordell_obstructions.json'
    path.write_text(json.dumps(out, indent=1) + '\n')
    print(f"{out['curves']} unresolved curves ({out['negative_k']} with k < 0): {out['category_counts']}")
    if join:
        print(f"  expert scan joined: {join['curves_joined']} curves, {join['nonempty_in_scan']} nonempty, "
              f"{join['signed_points_match_published']}/{join['with_published_count']} match the published count")
    for n, v in out['repairs_unlock'].items():
        print(f'  {n}: {v["count"]}')


if __name__ == '__main__':
    main()
