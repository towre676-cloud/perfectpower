"""Compare the positive-k Mordell point lists with seven original OEIS definitions.

Adapted from the second OEIS handoff (`recheck_positive_k_oeis.py`). The entries are read from
`data/oeis/seq` (unmodified copies, hashes in `data/oeis/manifest.json`):
* `A081119`: number of integral points of `y² = x³ + k` (signed `y`);
* `A134108`: number with `y ≥ 0`;
* `A054504`: the `k` with no integral point;
* `A134220`–`A134223`: the `k` with exactly 1, 2, 3, 4 distinct `x`-coordinates.

Theorem status comes from the axiom audit (`audit/axioms_report.txt`): a curve is
`lean_complete` when `Generated.ClassLists.K{k}.plus{k}` is audited on standard axioms.  OEIS
agreement is an independent regression, never a completeness proof.

Run: python3 python/positive_k_oeis.py  (writes receipts/positive_k_oeis.json)
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IDS = ('A081119', 'A134108', 'A054504', 'A134220', 'A134221', 'A134222', 'A134223')


def read_entry(aid):
    raw = (ROOT / 'data' / 'oeis' / 'seq' / aid[:4] / (aid + '.seq')).read_bytes()
    records = {}
    for line in raw.decode('utf-8').splitlines():
        if line.startswith('%') and line[3:10] == aid:
            records.setdefault(line[1], []).append(line[11:].strip())
    offset = int(records['O'][0].split(',')[0])
    terms = [int(s) for s in re.findall(r'-?\d+', ''.join(''.join(records.get(c, [])) for c in 'STU'))]
    assert terms and offset == 1, aid
    return {'id': aid, 'sha256': hashlib.sha256(raw).hexdigest(), 'name': records['N'][0],
            'offset': offset, 'terms': terms}


def lean_complete():
    """`k` with `ClassLists.K{k}.plus{k}` audited on the standard axioms."""
    out = set()
    for line in (ROOT / 'audit' / 'axioms_report.txt').read_text().splitlines():
        m = re.search(r"\.ClassLists\.K(\d+)\.plus(\d+)' depends on axioms: \[(.*)\]", line)
        if m and m.group(1) == m.group(2):
            assert set(a.strip() for a in m.group(3).split(',')) <= {'propext', 'Classical.choice', 'Quot.sound'}
            out.add(int(m.group(1)))
    return out


def run():
    source = json.loads((ROOT / 'receipts' / 'positive_k.json').read_text())
    entries = {aid: read_entry(aid) for aid in IDS}
    lean = lean_complete()
    by_id = {aid: {i + 1: v for i, v in enumerate(e['terms'])} for aid, e in entries.items()}
    # the set sequences are complete below their last listed value
    zero_set = set(entries['A054504']['terms'])
    x_sets = {j: set(entries[f'A13422{j - 1}']['terms']) for j in range(1, 5)}
    assert entries['A054504']['terms'] == sorted(zero_set) and entries['A054504']['terms'][-1] >= 100
    assert all(entries[f'A13422{j - 1}']['terms'][-1] >= 100 for j in range(1, 5))
    assert all(max(by_id[aid]) >= 100 for aid in ('A081119', 'A134108'))
    rows, failures = [], []
    for c in source['curves']:
        k = c['k']
        points = {tuple(p) for p in c['points_found']}
        assert len(points) == len(c['points_found'])
        assert all(y * y == x ** 3 + k for x, y in points) and all((x, -y) in points for x, y in points)
        total = len(points)
        nonneg = sum(y >= 0 for _, y in points)
        zero_y = sum(y == 0 for _, y in points)
        dx = len({x for x, _ in points})
        assert total == 2 * nonneg - zero_y and nonneg == dx
        checks = {'A081119_total': total == by_id['A081119'][k],
                  'A134108_nonnegative': nonneg == by_id['A134108'][k],
                  'A054504_empty_set': (total == 0) == (k in zero_set)}
        if dx in x_sets:
            checks['A13422x_distinct_x'] = k in x_sets[dx]
        checks['A13422x_unique_category'] = sum(k in s for s in x_sets.values()) == (dx in x_sets)
        if not all(checks.values()):
            failures.append({'k': k, 'checks': checks})
        rows.append({'k': k, 'theorem_status': 'lean_complete' if k in lean else 'census_only',
                     'total': total, 'nonnegative_y': nonneg, 'zero_y': zero_y, 'distinct_x': dx,
                     'checks': checks})
    assert len(rows) == 100
    return {
        'scope': 'OEIS original definitions vs receipts/positive_k.json points; an independent regression, '
                 'not a proof of the OEIS definitions or of completeness',
        'theorem_status_source': 'audit/axioms_report.txt (Generated.ClassLists.K{k}.plus{k})',
        'source_entries': {aid: {key: v for key, v in e.items() if key != 'terms'} for aid, e in entries.items()},
        'summary': {'curves': len(rows), 'matches': len(rows) - len(failures), 'mismatches': len(failures),
                    'lean_complete': sorted(lean), 'census_only_rows': sum(r['theorem_status'] == 'census_only' for r in rows)},
        'failures': failures,
        'rows': rows,
    }


if __name__ == '__main__':
    r = run()
    (ROOT / 'receipts' / 'positive_k_oeis.json').write_text(json.dumps(r, indent=1, sort_keys=True) + '\n')
    s = r['summary']
    print(f"positive k vs OEIS: {s['matches']}/{s['curves']} rows agree, {s['mismatches']} mismatches; "
          f"{len(s['lean_complete'])} Lean-complete, {s['census_only_rows']} census-only")
    if r['failures']:
        raise SystemExit('OEIS disagreement')
