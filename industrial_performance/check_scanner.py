"""Compare exact command slices and scanner cost on every pinned input byte."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))
from perfectpower.smt_cert import split_commands
from perfectpower.smt_stream import split_commands_fast


def task(spec):
    directory, entry, index = spec
    raw = (Path(directory)/entry['path']).read_bytes()
    if hashlib.sha256(raw).hexdigest() != entry['sha256']:
        raise ValueError('Source hash mismatch')
    source = raw.decode()
    results, seconds = {}, {}
    for mode in (['classic', 'fast'] if index % 2 == 0 else ['fast', 'classic']):
        started = time.perf_counter()
        results[mode] = (split_commands if mode == 'classic' else split_commands_fast)(source)
        seconds[mode] = time.perf_counter()-started
    if results['classic'] != results['fast']:
        raise ValueError(f"Command slice mismatch: {entry['path']}")
    digest = hashlib.sha256()
    for command in results['classic']:
        data = command.encode()
        digest.update(len(data).to_bytes(8, 'big'))
        digest.update(data)
    return dict(source=entry, commands=len(results['classic']), command_slices_sha256=digest.hexdigest(), seconds=seconds, exact_match=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--corpus', required=True)
    p.add_argument('--output', required=True)
    p.add_argument('--workers', type=int, default=3)
    args = p.parse_args()
    manifest = json.loads((Path(args.corpus)/'acquisition.json').read_text())
    entries = sorted(manifest['files'], key=lambda e: e['path'])
    if len(entries) != 181:
        raise ValueError('Expected 181 files')
    started = time.perf_counter()
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        rows = list(pool.map(task, [(args.corpus, entry, i) for i, entry in enumerate(entries)]))
    report = dict(complete=True, revision=manifest['revision'], workers=args.workers,
                  code_sha256={p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in
                    ['industrial_performance/check_scanner.py','python/perfectpower/smt_stream.py','python/perfectpower/smt_cert.py']},
                  files=len(rows), bytes=sum(r['source']['bytes'] for r in rows),
                  commands=sum(r['commands'] for r in rows), batch_seconds=time.perf_counter()-started,
                  seconds={mode: sum(r['seconds'][mode] for r in rows) for mode in ('classic', 'fast')}, rows=rows)
    Path(args.output).write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='rows'}), flush=True)
