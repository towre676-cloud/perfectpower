"""Per-query ledger of an independent SMT-LIB corpus through the fail-closed adapter
(`perfectpower.smt_cert`), joined with a file-level solver baseline.

Run: PYTHONPATH=<z3-solver>:python python3 python/nia_ledger.py HANDOFF_DIR [--baseline z3_*.json ...]
Writes receipts/nia_ledger.json (per-file ledgers, per-query rows, aggregates).
"""
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.smt_cert import ledger_for_file  # noqa: E402

COHORT = {'SMT-LIB__benchmark-submission': 'elster_industrial', 'cvc5__cvc5': 'cvc5_regression',
          'mikekben__STAUB': 'staub_crafted'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('handoff', type=Path)
    ap.add_argument('--baseline', action='append', default=[], type=Path)
    ap.add_argument('--out', type=Path, default=ROOT / 'receipts' / 'nia_ledger.json')
    a = ap.parse_args()
    corpus = a.handoff / 'corpus'
    base = {}
    for b in a.baseline:
        for row in json.loads(b.read_text()).get('results', []):
            base[row['local_path'].split('corpus/', 1)[-1]] = {
                k: row.get(k) for k in ('outcome', 'returncode', 'wall_seconds', 'query_count', 'fully_answered')} | {
                'statuses': {s: row.get('statuses', []).count(s) for s in ('sat', 'unsat', 'unknown')},
                'report': b.name}
    files = sorted(corpus.rglob('*.smt2'))
    rows, t0 = [], time.perf_counter()
    for f in files:
        rel = str(f.relative_to(corpus))
        led = ledger_for_file(f, rel)
        led['cohort'] = COHORT.get(rel.split('/')[0], 'other')
        led['baseline'] = base.get(rel)
        rows.append(led)
        print(f"{led['cohort']:18s} {rel[-60:]:60s} q={led.get('queries')} "
              f"cats={led.get('atom_categories', led.get('error'))}")
    agg = {}
    for c in sorted({r['cohort'] for r in rows}):
        rs = [r for r in rows if r['cohort'] == c]
        cats = {}
        for r in rs:
            for k, v in r.get('atom_categories', {}).items():
                cats[k] = cats.get(k, 0) + v
        agg[c] = {'files': len(rs), 'queries': sum(r.get('queries', 0) for r in rs),
                  'queries_with_nonlinear_live_atom': sum(1 for r in rs for q in r.get('per_query', [])
                                                          if q['categories'].get('nonlinear')),
                  'atom_categories': cats,
                  'nonlinear_atoms': sum(len(r.get('nonlinear_atoms', [])) for r in rs),
                  'unchecked_candidates': sum(1 for r in rs for x in r.get('nonlinear_atoms', [])
                                              if x['candidate'] and not x['checked']),
                  'checked_replacements': sum(len(r.get('certificates', [])) for r in rs),
                  'script_errors': sum('error' in r for r in rs)}
    out = {'label': 'independent corpus (upstream SMT-LIB files, byte-exact); fail-closed adapter; '
                    'checked replacements only where every condition in smt_cert holds',
           'handoff_manifest_sha256': hashlib.sha256((a.handoff / 'provenance' / 'upstream.json').read_bytes()).hexdigest()
           if (a.handoff / 'provenance' / 'upstream.json').exists() else None,
           'analysis_seconds_total': round(time.perf_counter() - t0, 2),
           'aggregate': agg, 'files': rows}
    a.out.write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(agg, indent=1))


if __name__ == '__main__':
    main()
