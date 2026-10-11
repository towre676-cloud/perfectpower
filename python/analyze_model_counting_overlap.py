#!/usr/bin/env python3
"""Secondary descriptive strata after a normalized corpus-overlap audit."""
import argparse
import hashlib
import json
from pathlib import Path
from analyze_model_counting_comparison import analyze
from compare_model_counting import summarize


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--receipt', type=Path, required=True)
    p.add_argument('--overlap', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    raw = a.receipt.read_bytes(); receipt = json.loads(raw)
    audit_raw = a.overlap.read_bytes(); audit = json.loads(audit_raw)
    if not receipt['completed']:
        raise ValueError('completed evaluation required')
    if audit['schema'] != 'pp-cnf-overlap/1':
        raise ValueError('unknown overlap audit')
    if audit['evaluation_manifest_sha256'] != receipt['source_identities']['manifest']:
        raise ValueError('overlap audit uses a different evaluation manifest')
    if {r['name'] for r in audit['evaluation_instances']} != set(receipt['instances']):
        raise ValueError('overlap audit must cover the complete evaluation scope')
    matched = {r['name'] for r in audit['evaluation_instances'] if r['normalized_repeats']}
    report = {'schema': 'pp-cnf-overlap-analysis/1',
              'receipt_sha256': hashlib.sha256(raw).hexdigest(),
              'overlap_sha256': hashlib.sha256(audit_raw).hexdigest(),
              'scope': 'Secondary strata determined by normalized overlap; no-match does not establish semantic or family novelty; primary full-corpus ledger remains unchanged',
              'strata': {}}
    for label, select in [('normalized_match', matched),
                          ('no_normalized_match', set(receipt['instances'])-matched)]:
        names = [n for n in receipt['instances'] if n in select]
        subset = dict(receipt, instances=names,
                      results=[r for r in receipt['results'] if r['name'] in select])
        report['strata'][label] = {
            'instances': len(names),
            'summary': summarize(subset['results'], receipt['solver_scope'], receipt['timeout_seconds']),
            'comparisons': [analyze(subset, s) for s in receipt['solver_scope'] if s != 'perfectpower'] if names else []}
    a.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
