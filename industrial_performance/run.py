"""Frozen per-file prefix, paired independent executions, complete raw query ledger."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import platform
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))
from perfectpower.industrial_portfolio import solve_stream
from perfectpower.smt_cert import split_commands, head
import z3


def task(spec):
    directory, entry, cap, timeout, index = spec
    raw = (Path(directory) / entry['path']).read_bytes()
    if hashlib.sha256(raw).hexdigest() != entry['sha256']:
        raise ValueError('Source hash mismatch')
    commands = split_commands(raw.decode())
    full_count = sum(head(c) in ('check-sat', 'check-sat-assuming') for c in commands)
    prefix, count = [], 0
    for command in commands:
        prefix.append(command)
        count += head(command) in ('check-sat', 'check-sat-assuming')
        if count == cap:
            break
    source = '\n'.join(prefix) + '\n'
    results = {}
    for mode in (['original', 'portfolio'] if index % 2 == 0 else ['portfolio', 'original']):
        results[mode] = solve_stream(source, timeout, portfolio=mode == 'portfolio')
        if results[mode]['errors'] or len(results[mode]['queries']) != count:
            raise ValueError(f"Invalid stream {entry['path']}: {results[mode]}")
    return dict(source=entry, full_query_count=full_count, selected_queries=count,
                prefix_sha256=hashlib.sha256(source.encode()).hexdigest(), **results)


def summary(rows):
    counts = {mode: {answer: 0 for answer in ('sat', 'unsat', 'unknown')} for mode in ('original', 'portfolio')}
    conflicts, gains, losses = 0, 0, 0
    for row in rows:
        for a, b in zip(row['original']['queries'], row['portfolio']['queries']):
            counts['original'][a['answer']] += 1
            counts['portfolio'][b['answer']] += 1
            conflicts += {a['answer'], b['answer']} == {'sat', 'unsat'}
            gains += a['answer'] == 'unknown' and b['answer'] != 'unknown'
            losses += a['answer'] != 'unknown' and b['answer'] == 'unknown'
    wall = {mode: sum(r[mode]['wall_seconds'] for r in rows) for mode in counts}
    return dict(files=len(rows), queries=sum(r['selected_queries'] for r in rows), counts=counts,
                wall_seconds=wall, solved_delta=gains-losses, gains=gains, losses=losses,
                sat_unsat_conflicts=conflicts, eligible_files=sum(r['portfolio']['eligible'] for r in rows))


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--corpus', required=True)
    p.add_argument('--cap', type=int, default=8)
    p.add_argument('--timeout-ms', type=int, default=250)
    p.add_argument('--workers', type=int, default=3)
    p.add_argument('--output', required=True)
    args = p.parse_args()
    if args.cap < 1 or args.timeout_ms < 2 or args.workers < 1:
        p.error('Invalid positive execution bounds')
    manifest = json.loads((Path(args.corpus) / 'acquisition.json').read_text())
    entries = sorted(manifest['files'], key=lambda e: e['path'])
    if len(entries) != 181:
        raise ValueError('Expected complete 181-file cohort')
    started = time.perf_counter()
    rows = []
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    specs = [(args.corpus, e, args.cap, args.timeout_ms, i) for i, e in enumerate(entries)]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for row in pool.map(task, specs):
            rows.append(row)
            checkpoint = output.with_suffix('.checkpoint.json')
            checkpoint.write_text(json.dumps(dict(complete=False, rows=rows)))
            if len(rows) % 20 == 0:
                print(f'{len(rows)}/181 files', flush=True)
    report = dict(complete=True, revision=manifest['revision'], cap=args.cap,
                  timeout_ms=args.timeout_ms, workers=args.workers, z3=z3.get_version_string(),
                  platform=platform.platform(), python=sys.version, batch_seconds=time.perf_counter()-started,
                  protocol='First min(cap, query_count) per file; alternating fresh contexts; query-only timeout; candidate classification and dual-context maintenance included.',
                  summary=summary(rows), rows=rows)
    output.write_text(json.dumps(report, indent=2) + '\n')
    output.with_suffix('.checkpoint.json').unlink()
    print(json.dumps(report['summary']), flush=True)
