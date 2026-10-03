"""Paired industrial transport experiment with hash-bound resumable checkpoints."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import platform
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))
from perfectpower.industrial_replay import solve_replay
from perfectpower.smt_cert import split_commands, head
import z3


def task(spec):
    directory, entry, cap, timeout, bound, index, fast_split = spec
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
    order = ['command', 'batched'] if index % 2 == 0 else ['batched', 'command']
    for mode in order:
        results[mode] = solve_replay(source, timeout, batch_chars=0 if mode == 'command' else bound,
                                     fast_split=fast_split and mode == 'batched')
        if results[mode]['errors'] or len(results[mode]['queries']) != count:
            raise ValueError(f"Invalid stream {entry['path']}: {results[mode]}")
    return dict(source=entry, full_query_count=full_count, selected_queries=count,
                prefix_sha256=hashlib.sha256(source.encode()).hexdigest(), order=order, **results)


def summarize(rows):
    counts = {mode: {answer: 0 for answer in ('sat', 'unsat', 'unknown')} for mode in ('command', 'batched')}
    conflicts = gains = losses = 0
    for row in rows:
        for a, b in zip(row['command']['queries'], row['batched']['queries']):
            counts['command'][a['answer']] += 1
            counts['batched'][b['answer']] += 1
            conflicts += {a['answer'], b['answer']} == {'sat', 'unsat'}
            gains += a['answer'] == 'unknown' and b['answer'] != 'unknown'
            losses += a['answer'] != 'unknown' and b['answer'] == 'unknown'
    totals = {mode: {metric: sum(r[mode][metric] for r in rows) for metric in
              ('wall_seconds', 'parse_seconds', 'ingestion_seconds', 'query_seconds', 'native_calls', 'ingestion_calls')}
              for mode in counts}
    return dict(files=len(rows), queries=sum(r['selected_queries'] for r in rows), counts=counts,
                totals=totals, gains=gains, losses=losses, solved_delta=gains-losses,
                sat_unsat_conflicts=conflicts,
                faster_files=sum(r['batched']['wall_seconds'] < r['command']['wall_seconds'] for r in rows))


def write_atomic(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    with temporary.open('w') as f:
        json.dump(value, f, indent=2)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    temporary.replace(path)


def validate_checkpoint(saved, config, entries):
    if saved.get('config') != config or saved.get('complete') is not False:
        raise ValueError('Checkpoint protocol, sources, engine, or environment changed')
    rows = saved.get('rows', [])
    if len(rows) > len(entries):
        raise ValueError('Too many checkpoint rows')
    for i, row in enumerate(rows):
        if row['source'] != entries[i] or row['selected_queries'] != min(config['cap'], row['full_query_count']):
            raise ValueError('Checkpoint source or query selection mismatch')
        for mode in ('command', 'batched'):
            if row[mode]['errors'] or len(row[mode]['queries']) != row['selected_queries']:
                raise ValueError('Invalid checkpoint query stream')
            if any(q['answer'] not in ('sat', 'unsat', 'unknown') for q in row[mode]['queries']):
                raise ValueError('Invalid checkpoint answer')
    return rows


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--corpus', required=True)
    p.add_argument('--cap', type=int, default=8)
    p.add_argument('--timeout-ms', type=int, default=250)
    p.add_argument('--workers', type=int, default=3)
    p.add_argument('--batch-chars', type=int, default=262144)
    p.add_argument('--output', required=True)
    p.add_argument('--resume', action='store_true')
    p.add_argument('--fast-split', action='store_true')
    args = p.parse_args()
    if min(args.cap, args.workers, args.batch_chars) < 1 or args.timeout_ms < 2:
        p.error('Invalid execution bounds')
    manifest_path = Path(args.corpus) / 'acquisition.json'
    manifest = json.loads(manifest_path.read_text())
    entries = sorted(manifest['files'], key=lambda e: e['path'])
    if len(entries) != 181:
        raise ValueError('Expected complete 181-file cohort')
    code_paths = ['industrial_performance/run_replay.py', 'python/perfectpower/industrial_replay.py', 'python/perfectpower/smt_cert.py', 'python/perfectpower/smt_stream.py']
    config = dict(revision=manifest['revision'], manifest_sha256=hashlib.sha256(manifest_path.read_bytes()).hexdigest(),
                  cap=args.cap, timeout_ms=args.timeout_ms, workers=args.workers, batch_chars=args.batch_chars,
                  fast_split=args.fast_split,
                  z3=z3.get_version_string(), python=sys.version, platform=platform.platform(),
                  code_sha256={name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in code_paths})
    output = Path(args.output)
    output.parent.mkdir(parents=True, exist_ok=True)
    checkpoint = output.with_suffix('.checkpoint.json')
    rows = validate_checkpoint(json.loads(checkpoint.read_text()), config, entries) if args.resume and checkpoint.exists() else []
    resumed_rows = len(rows)
    started = time.perf_counter()
    specs = [(args.corpus, entries[i], args.cap, args.timeout_ms, args.batch_chars, i, args.fast_split) for i in range(len(rows), len(entries))]
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        for row in pool.map(task, specs):
            rows.append(row)
            write_atomic(checkpoint, dict(complete=False, config=config, rows=rows))
            if len(rows) % 20 == 0:
                print(f'{len(rows)}/181 files', flush=True)
    report = dict(complete=True, config=config, resumed_rows=resumed_rows,
                  current_batch_seconds=time.perf_counter()-started,
                  protocol='First min(cap, query_count) per file; alternating fresh identical Z3 contexts; same configured query allocation; original commands unchanged; candidate batches non-query transport and optionally accelerates exact command slicing; syntax splitting and context setup included in wall sums.',
                  summary=summarize(rows), rows=rows)
    write_atomic(output, report)
    checkpoint.unlink(missing_ok=True)
    print(json.dumps(report['summary']), flush=True)
