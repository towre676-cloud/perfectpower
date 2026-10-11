#!/usr/bin/env python3
"""Frozen, paired, serial comparison against a prior checkout and references.

Writes portable per-case receipts; detailed local logs stay outside the source
release. Every declared instance remains in the denominator, including limits.
"""
import argparse
import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

from run_model_counting import ROOT, acquire_output_lock, native_library, run


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def summarize(results, solvers, timeout):
    summary = {}
    for solver in solvers:
        outcomes = [r['solvers'][solver] for r in results]
        summary[solver] = {
            'outcomes': {status: sum(o['status'] == status for o in outcomes)
                         for status in sorted({o['status'] for o in outcomes})},
            'par2_seconds': sum(o['seconds'] if o['status'] == 'EXACT'
                                else 2 * timeout for o in outcomes),
        }
    if 'previous' in solvers:
        summary['paired_change'] = {
            'gained': [r['name'] for r in results if r['solvers']['perfectpower']['status'] == 'EXACT'
                       and r['solvers']['previous']['status'] != 'EXACT'],
            'lost': [r['name'] for r in results if r['solvers']['previous']['status'] == 'EXACT'
                     and r['solvers']['perfectpower']['status'] != 'EXACT'],
        }
    return summary


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest', type=Path, required=True)
    p.add_argument('--corpus', type=Path, required=True)
    p.add_argument('--previous-root', type=Path, required=True)
    p.add_argument('--ganak', type=Path)
    p.add_argument('--d4', type=Path)
    p.add_argument('--timeout', type=float, default=5)
    p.add_argument('--memory-gib', type=int, default=6)
    p.add_argument('--repetitions', type=int, default=1)
    p.add_argument('--names', nargs='+', help='Explicit scope fixed before measurement')
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--log-directory', type=Path, required=True)
    p.add_argument('--stop-file', type=Path)
    args = p.parse_args()
    if not 0 < args.timeout <= 3600 or not 1 <= args.memory_gib <= 32 or not 1 <= args.repetitions <= 20:
        p.error('bounded time, memory and repetitions required')
    args.output = args.output.resolve()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    # All comparisons share this lock, regardless of their chosen output.
    with acquire_output_lock(ROOT / 'receipts/model_counting/comparison-serial'):
        if args.output.exists():
            raise RuntimeError('refusing to overwrite an experiment receipt')
        manifest = json.loads(args.manifest.read_text())
        rows = manifest['instances']
        if args.names:
            selected = set(args.names)
            if len(selected) != len(args.names) or selected - {r['name'] for r in rows}:
                raise ValueError('unknown or duplicate declared names')
            rows = [r for r in rows if r['name'] in selected]
        if not rows:
            raise ValueError('empty comparison scope')
        previous = args.previous_root.resolve()
        paths = {
            'counter': ROOT / 'native/model_counting/counter.cpp',
            'python': ROOT / 'python/perfectpower/model_counting.py',
            'runner': Path(__file__).resolve(),
            'execution': ROOT / 'python/run_model_counting.py',
            'previous_counter': previous / 'native/model_counting/counter.cpp',
            'previous_python': previous / 'python/perfectpower/model_counting.py',
            'previous_worker': previous / 'python/run_model_counting.py',
            'manifest': args.manifest.resolve(),
        }
        identities = {k: digest(v) for k, v in paths.items()}
        library = native_library()
        warmed = subprocess.run([sys.executable, '-c',
                        'import sys;sys.path.insert(0,sys.argv[1]);'
                        'from perfectpower.model_counting import native_library;print(native_library()._name)',
                        str(previous / 'python')], check=True, capture_output=True, text=True)
        paths['native_binary'] = Path(library._name)
        paths['previous_native_binary'] = Path(warmed.stdout.strip())
        identities.update({k: digest(paths[k]) for k in ('native_binary', 'previous_native_binary')})
        solvers = {
            'perfectpower': [sys.executable, str(ROOT / 'python/run_model_counting.py'), '--worker'],
            'previous': [sys.executable, str(previous / 'python/run_model_counting.py'), '--worker'],
        }
        if args.ganak:
            solvers['ganak'] = [str(args.ganak.resolve()), '--prob', '0']
            identities['ganak_binary'] = digest(args.ganak)
            paths['ganak_binary'] = args.ganak.resolve()
        if args.d4:
            solvers['d4_2024'] = [str(args.d4.resolve())]
            identities['d4_binary'] = digest(args.d4)
            paths['d4_binary'] = args.d4.resolve()
        receipt = {
            'schema': 'pp-cnf-paired/1', 'started_utc': datetime.now(timezone.utc).isoformat(),
            'dataset': manifest['dataset'], 'instances': [r['name'] for r in rows],
            'source_identities': identities, 'timeout_seconds': args.timeout,
            'memory_gib': args.memory_gib, 'repetitions': args.repetitions,
            'timing_scope': 'Serial cold subprocess wall time, including parsing and construction; native compilation warmed separately',
            'solver_scope': list(solvers),
            'reference_scope': 'Ganak 2.8.0 deterministic; D4 archived 2024 entry, not a current-champion comparison',
            'results': [], 'completed': False,
        }
        logs = args.log_directory.resolve()
        logs.mkdir(parents=True, exist_ok=True)

        def save():
            tmp = args.output.with_suffix('.tmp')
            tmp.write_text(json.dumps(receipt, indent=2) + '\n')
            tmp.replace(args.output)

        save()  # Fix identities, all instances, limits and repeats before results.
        for trial in range(args.repetitions):
            for i, row in enumerate(rows):
                if args.stop_file and args.stop_file.exists():
                    raise RuntimeError('stopped by requested stop file')
                if any(digest(path) != identities[k] for k, path in paths.items()):
                    raise RuntimeError('frozen experiment identity changed')
                path = args.corpus / row['name']
                if digest(path) != row['sha256']:
                    raise ValueError('corpus identity changed: ' + row['name'])
                result = {'name': row['name'], 'sha256': row['sha256'], 'trial': trial,
                          'overlap_mc2024': row.get('overlap_mc2024'), 'solvers': {}}
                order = list(solvers)
                rotation = (i + trial) % len(order)
                order = order[rotation:] + order[:rotation]
                for solver in order:
                    command = solvers[solver] + [str(path)]
                    if solver in ('perfectpower', 'previous'):
                        command += ['--timeout', str(args.timeout)]
                    if solver == 'd4_2024':
                        command += ['-mc']
                    log = logs / f'{row["name"]}.{trial}.{solver}.log'
                    answer = run(command, args.timeout, args.memory_gib * 1024**3, log)
                    # Environment-derived command lines and full logs are local.
                    answer.pop('command', None)
                    answer['log'] = log.name
                    answer['log_sha256'] = digest(log)
                    result['solvers'][solver] = answer
                exact = [o['count'] for o in result['solvers'].values() if o['status'] == 'EXACT']
                result['agreement'] = ('MISMATCH' if len(set(exact)) > 1 else
                                       'MATCH' if len(exact) > 1 else 'UNCONFIRMED')
                receipt['results'].append(result)
                receipt['summary'] = summarize(receipt['results'], solvers, args.timeout)
                save()
                print(f'{trial + 1}/{args.repetitions} {i + 1}/{len(rows)} {row["name"]}: '
                      + ', '.join(f'{s}={o["status"]}:{o["seconds"]:.3f}'
                                  for s, o in result['solvers'].items()), flush=True)
                if result['agreement'] == 'MISMATCH':
                    raise RuntimeError('exact count disagreement: ' + row['name'])
        receipt['completed'] = True
        receipt['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
        print(json.dumps(receipt['summary']), flush=True)


if __name__ == '__main__':
    main()
