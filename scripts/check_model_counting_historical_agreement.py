#!/usr/bin/env python3
"""Audit new MC2024 exact answers against the pinned historical reference ledger.

The ten-second reference outcomes validate counts, not five-second rankings.
Original logs are audited separately by check_model_counting_receipts.py.
"""
import argparse
import hashlib
import json
from pathlib import Path


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--current', type=Path, required=True)
    p.add_argument('--historical', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    raw = a.current.read_bytes(); current = json.loads(raw)
    old_raw = a.historical.read_bytes(); old = json.loads(old_raw)
    if not current['completed'] or not old['completed']:
        raise ValueError('both complete ledgers required')
    index = {r['name']: r for r in old['results']}
    rows = []
    for r in current['results']:
        answer = r['solvers']['perfectpower']
        if answer['status'] != 'EXACT':
            continue
        prior = index[r['name']]
        if r['sha256'] != prior['sha256']:
            raise ValueError('input identity differs')
        references = [s for s in ['ganak', 'd4'] if prior['solvers'][s]['status'] == 'EXACT']
        if any(prior['solvers'][s]['count'] != answer['count'] for s in references):
            raise ValueError('historical count disagreement')
        rows.append({'name': r['name'], 'trial': r['trial'], 'sha256': r['sha256'],
                     'count': answer['count'], 'historical_exact_references': references,
                     'agreement': 'MATCH' if references else 'UNCONFIRMED'})
    report = {'schema': 'pp-cnf-historical-agreement/1',
              'current_sha256': hashlib.sha256(raw).hexdigest(),
              'historical_sha256': hashlib.sha256(old_raw).hexdigest(),
              'scope': 'Independent historical count validation only; differing deadlines cannot establish current timing advantages',
              'results': rows,
              'confirmed': sum(bool(r['historical_exact_references']) for r in rows),
              'unconfirmed': sum(not r['historical_exact_references'] for r in rows)}
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'confirmed': report['confirmed'], 'unconfirmed': report['unconfirmed']}))


if __name__ == '__main__':
    main()
