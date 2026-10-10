#!/usr/bin/env python3
"""Repeat every independently confirmed native case, including observed losses."""
import argparse
import hashlib
import json
import re
import statistics
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from run_model_counting import ROOT, acquire_output_lock, native_library, run


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--time-binary', type=Path, default=Path('/usr/bin/time'))
    parser.add_argument('--profile-memory', action='store_true')
    parser.add_argument('--screen', type=Path, required=True)
    parser.add_argument('--corpus', type=Path, required=True)
    parser.add_argument('--ganak', type=Path, required=True)
    parser.add_argument('--d4', type=Path, required=True)
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--output', type=Path, default=ROOT / 'receipts/model_counting/repeated.json')
    args = parser.parse_args()
    screen = json.loads(args.screen.read_text())
    if args.profile_memory and not args.time_binary.is_file():
        raise ValueError('GNU time binary required for peak memory profiling')
    if not screen.get('completed'):
        raise ValueError('completed screen required')
    if not 1 <= args.repeats <= 10:
        raise ValueError('repeat count 1..10 required')
    if sha(ROOT / 'native/model_counting/counter.cpp') != screen['native_source_sha256'] or sha(ROOT / 'python/perfectpower/model_counting.py') != screen['python_source_sha256']:
        raise ValueError('screen counter differs')
    native_library()
    output = args.output.resolve()
    logs = output.parent / (output.stem + '_logs')
    logs.mkdir(parents=True, exist_ok=True)
    output_lock = acquire_output_lock(output)
    selected = [row for row in screen['results']
                if row['agreement'] == 'MATCH' and row['solvers']['perfectpower']['status'] == 'EXACT']
    data = {
        'schema': 'pp-cnf-repeated/1',
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'screen_sha256': sha(args.screen),
        'additional_control': 'Ganak --prob 1, its documented probabilistic default mode; same pinned binary',
        'selection': 'Every independently confirmed PerfectPower exact case from the full screen, including losses; no speed-based filtering',
        'instances': [row['name'] for row in selected],
        'repeats': args.repeats,
        'timeout_seconds': screen['timeout_seconds'],
        'memory_gib': screen['memory_gib'],
        'memory_profile': args.profile_memory,
        'time_binary_sha256': sha(args.time_binary) if args.profile_memory else None,
        'timing_scope': 'cold subprocess with compiler warmed; GNU time wrapper included equally when profiling memory',
        'native_source_sha256': screen['native_source_sha256'],
        'python_source_sha256': screen['python_source_sha256'],
        'results': [],
    }

    def save():
        temporary = output.with_suffix('.tmp')
        temporary.write_text(json.dumps(data, indent=2) + '\n')
        temporary.replace(output)

    save()  # Fix the entire repeat scope before measuring any selected case.
    for case, row in enumerate(selected):
        path = args.corpus / row['name']
        if sha(path) != row['sha256']:
            raise ValueError('input hash differs')
        eligible = ['perfectpower'] + [s for s in ('ganak', 'd4') if s in screen['solvers']] + ['ganak_probabilistic']
        result = {
            'name': row['name'],
            'sha256': row['sha256'],
            'expected_count': row['solvers']['perfectpower']['count'],
            'trials': {solver: [] for solver in eligible},
        }
        for trial in range(args.repeats):
            offset = (case + trial) % len(eligible)
            order = eligible[offset:] + eligible[:offset]
            for solver in order:
                if solver == 'perfectpower':
                    command = [sys.executable, str(ROOT / 'python/run_model_counting.py'), '--worker', str(path), '--timeout', str(screen['timeout_seconds'])]
                elif solver in ('ganak', 'ganak_probabilistic'):
                    command = [str(args.ganak.resolve()), '--prob', '1' if solver == 'ganak_probabilistic' else '0', str(path)]
                else:
                    command = [str(args.d4.resolve()), str(path), '-mc']
                identity = 'ganak' if solver == 'ganak_probabilistic' else solver
                if sha(Path(command[0])) != screen['solvers'][identity]['binary_sha256']:
                    raise ValueError('reference/interpreter binary differs')
                memory_file = logs / f'{row["name"]}.{solver}.{trial}.memory.log'
                measured = [str(args.time_binary.resolve()), '-v', '-o', str(memory_file)] + command if args.profile_memory else command
                answer = run(measured, screen['timeout_seconds'], screen['memory_gib'] * 1024**3, logs / f'{row["name"]}.{solver}.{trial}.log')
                if args.profile_memory and memory_file.exists():
                    match = re.search(r'Maximum resident set size \(kbytes\): (\d+)', memory_file.read_text())
                    answer['peak_rss_kib'] = int(match[1]) if match else None
                if answer['status'] == 'EXACT' and answer['count'] != result['expected_count']:
                    raise RuntimeError('repeat exact count disagreement')
                result['trials'][solver].append(answer)
                print(f'{case + 1}/{len(selected)} {row["name"]} trial {trial + 1} {solver}: {answer["status"]} {answer["seconds"]:.3f}s', flush=True)
        result['median_seconds'] = {
            solver: statistics.median(a['seconds'] for a in answers)
            if all(a['status'] == 'EXACT' for a in answers) else None
            for solver, answers in result['trials'].items()
        }
        result['median_peak_rss_kib'] = {
            solver: statistics.median(a['peak_rss_kib'] for a in answers)
            if all(a.get('peak_rss_kib') is not None and a['status'] == 'EXACT' for a in answers) else None
            for solver, answers in result['trials'].items()
        }
        data['results'].append(result)
        save()
    data['completed'] = True
    save()


if __name__ == '__main__':
    main()
