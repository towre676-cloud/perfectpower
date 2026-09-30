"""Query-level timing of SMT-LIB scripts with z3's own SMT-LIB interpreter.

Each file runs in a fresh z3 context.  Its commands are fed one at a time
(`Z3_eval_smtlib2_string`), so push/pop and incremental state are z3's native semantics.  Every
`check-sat` is timed separately under its own timeout, set through `(set-option :timeout ms)`
before the file's commands.  Harness directives in comments are never executed.  A per-file
wall-clock budget stops a file early; the remaining queries are recorded as `not_run`, never
estimated.

Run: PYTHONPATH=<z3-solver>:python python3 python/nia_query_timing.py HANDOFF_DIR
         [--query-timeout 2] [--file-budget 120] [--cohort elster|cvc5|staub|all]
Writes receipts/nia_query_timing.json.
"""
import argparse
import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

import z3  # noqa: E402

from perfectpower.smt_cert import head, split_commands  # noqa: E402

PREFIX = {'elster': 'SMT-LIB__benchmark-submission', 'cvc5': 'cvc5__cvc5', 'staub': 'mikekben__STAUB'}


def run_file(path: Path, qto_ms: int, budget: float) -> dict:
    raw = path.read_bytes()
    cmds = split_commands(raw.decode('utf-8'))
    ctx = z3.Context()
    ev = lambda s: z3.Z3_eval_smtlib2_string(ctx.ref(), s)  # noqa: E731
    rows, t_file, err = [], time.perf_counter(), None
    try:
        ev(f'(set-option :timeout {qto_ms})')
    except z3.Z3Exception as ex:
        err = str(ex)
    for i, c in enumerate(cmds):
        h = head(c)
        if h in ('check-sat', 'check-sat-assuming'):
            if time.perf_counter() - t_file > budget:
                rows.append({'command_index': i, 'result': 'not_run', 'seconds': None})
                continue
            t = time.perf_counter()
            try:
                res = ev(c).strip()
            except z3.Z3Exception as ex:
                res = 'error: ' + str(ex)[:120]
            rows.append({'command_index': i, 'result': res.splitlines()[-1] if res else '', 'seconds': round(time.perf_counter() - t, 4)})
        elif h in ('exit',):
            break
        elif h in ('get-model', 'get-value', 'get-info', 'get-unsat-core', 'get-proof', 'echo'):
            continue            # outputs are not needed for timing
        else:
            try:
                ev(c)
            except z3.Z3Exception as ex:
                err = err or f'command {i} ({h}): {str(ex)[:160]}'
    del ctx
    tally = {}
    for r in rows:
        k = r['result'] if r['result'] in ('sat', 'unsat', 'unknown', 'not_run') else 'error'
        tally[k] = tally.get(k, 0) + 1
    timed = [r['seconds'] for r in rows if r['seconds'] is not None]
    return {'sha256': hashlib.sha256(raw).hexdigest(), 'queries': len(rows), 'tally': tally,
            'query_seconds_total': round(sum(timed), 3), 'query_seconds_max': max(timed, default=0),
            'file_wall_seconds': round(time.perf_counter() - t_file, 3), 'first_error': err, 'per_query': rows}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('handoff', type=Path)
    ap.add_argument('--query-timeout', type=float, default=2.0)
    ap.add_argument('--file-budget', type=float, default=120.0)
    ap.add_argument('--cohort', default='all')
    ap.add_argument('--out', type=Path, default=ROOT / 'receipts' / 'nia_query_timing.json')
    a = ap.parse_args()
    corpus = a.handoff / 'corpus'
    files = sorted(corpus.rglob('*.smt2'))
    if a.cohort != 'all':
        files = [f for f in files if str(f.relative_to(corpus)).startswith(PREFIX[a.cohort])]
    out = {'solver': f'z3 {z3.get_version_string()} (Python API, SMT-LIB interpreter, command by command)',
           'query_timeout_s': a.query_timeout, 'file_budget_s': a.file_budget, 'files': {}}
    for f in files:
        rel = str(f.relative_to(corpus))
        r = run_file(f, int(a.query_timeout * 1000), a.file_budget)
        out['files'][rel] = r
        print(f"{rel[-55:]:55s} q={r['queries']:5d} {r['tally']} total {r['query_seconds_total']}s max {r['query_seconds_max']}s")
        a.out.write_text(json.dumps(out, indent=1) + '\n')


if __name__ == '__main__':
    main()
