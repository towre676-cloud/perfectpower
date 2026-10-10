#!/usr/bin/env python3
"""Audit completed benchmark receipts against their original source identities."""
import argparse
import hashlib
import json
import re
import statistics
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def exact_from_log(path):
    stdout = path.read_text().split('\n--- STDERR ---\n', 1)[0]
    matches = re.findall(r'^c s exact arb int ([0-9]+)\s*$', stdout, re.M)
    if not matches:
        matches = re.findall(r'^s (?:mc )?([0-9]+)\s*$', stdout, re.M)
    if matches:
        return matches[-1]
    answer = json.loads(stdout.strip())
    require(answer['status'] == 'EXACT', 'nonexact native log: ' + str(path))
    value = answer['count']
    require(isinstance(value, str) and value.isascii() and value.isdigit(), 'invalid decimal log count')
    return value

def check(log_root=ROOT):
    log_root = Path(log_root)
    folder = ROOT / 'receipts/model_counting'
    screen_path = folder / 'benchmark.json'
    screen = json.loads(screen_path.read_text())
    manifest_path = ROOT / 'data/model_counting/manifest.json'
    manifest = json.loads(manifest_path.read_text())
    references = json.loads((ROOT / 'data/model_counting/references.json').read_text())
    require(screen.get('completed') is True, 'screen incomplete')
    require(screen['split'] == 'all' and screen['limit'] is None, 'full original corpus required')
    require(screen['manifest_sha256'] == sha(manifest_path), 'manifest identity differs')
    names = [row['name'] for row in manifest['instances']]
    require(len(names) == 200 and screen['instances'] == names, 'original 200-case scope differs')
    require([row['name'] for row in screen['results']] == names, 'measured scope differs')
    require(screen['timeout_seconds'] == 10 and screen['memory_gib'] == 6, 'declared latency contract differs')
    for field, name in [('native_source_sha256', 'native/model_counting/counter.cpp'),
                        ('python_source_sha256', 'python/perfectpower/model_counting.py')]:
        require(screen[field] == sha(ROOT / name), 'frozen source differs: ' + name)
    for solver in ('ganak', 'd4'):
        require(screen['solvers'][solver]['binary_sha256'] == references[solver]['binary_sha256'], 'reference differs: ' + solver)
    audited_logs = 0
    confirmed = []
    for row, original in zip(screen['results'], manifest['instances']):
        require(row['sha256'] == original['sha256'] and row['split'] == original['split'], 'input identity differs')
        exact = []
        require(set(row['solvers']) == set(screen['solvers']), 'solver scope differs')
        for solver, answer in row['solvers'].items():
            path = log_root / answer['log']
            require(path.is_file(), 'missing raw log')
            if answer['status'] == 'EXACT':
                require(answer['exit_code'] == 0, 'exact result from failed subprocess')
                require(exact_from_log(path) == answer['count'], 'count/log disagreement')
                exact.append(answer['count'])
            else:
                require(answer['count'] is None, 'nonexact outcome carries a count')
            audited_logs += 1
        require(len(set(exact)) <= 1, 'independent count disagreement')
        agreement = 'MATCH' if len(exact) >= 2 else 'UNCONFIRMED'
        require(row['agreement'] == agreement, 'agreement classification differs')
        if agreement == 'MATCH' and row['solvers']['perfectpower']['status'] == 'EXACT':
            confirmed.append(row['name'])
    for solver, summary in screen['summary'].items():
        expected = {status: sum(r['solvers'][solver]['status'] == status for r in screen['results'])
                    for status in {r['solvers'][solver]['status'] for r in screen['results']}}
        require(summary == expected, 'summary differs')
    repeated = json.loads((folder / 'repeated.json').read_text())
    require(repeated.get('completed') is True and repeated['screen_sha256'] == sha(screen_path), 'repeat screen identity differs')
    require(repeated['native_source_sha256'] == screen['native_source_sha256'] and repeated['python_source_sha256'] == screen['python_source_sha256'], 'repeat source differs')
    require(repeated['instances'] == confirmed, 'preregistered repeat scope differs')
    require(repeated['timeout_seconds'] == 10 and repeated['memory_gib'] == 6, 'repeat resource contract differs')
    require(repeated['repeats'] == 3 and repeated['memory_profile'] is True, 'three memory-profiled trials required')
    require([r['name'] for r in repeated['results']] == confirmed, 'repeat subset filters confirmed cases')
    by_name = {r['name']: r for r in screen['results']}
    for row in repeated['results']:
        original = by_name[row['name']]
        require(row['sha256'] == original['sha256'], 'repeat input differs')
        require(row['expected_count'] == original['solvers']['perfectpower']['count'], 'repeat expected count differs')
        require(set(row['trials']) == {'perfectpower', 'ganak', 'd4', 'ganak_probabilistic'}, 'repeat control missing')
        for solver, trials in row['trials'].items():
            require(len(trials) == 3, 'repeat trial count differs')
            for trial in trials:
                path = log_root / trial['log']
                require(path.is_file(), 'missing repeat raw log')
                if trial['status'] == 'EXACT':
                    require(exact_from_log(path) == trial['count'] == row['expected_count'], 'repeat count disagreement')
                else:
                    require(trial['count'] is None, 'nonexact trial carries count')
                if trial.get('peak_rss_kib') is not None:
                    memory_path = path.with_name(path.stem + '.memory.log')
                    match = re.search(r'Maximum resident set size \(kbytes\): (\d+)', memory_path.read_text())
                    require(match is not None and int(match[1]) == trial['peak_rss_kib'], 'memory/log disagreement')
                audited_logs += 1
            all_exact = all(t['status'] == 'EXACT' for t in trials)
            median = statistics.median(t['seconds'] for t in trials) if all_exact else None
            require(row['median_seconds'][solver] == median, 'time median differs')
            memory_median = statistics.median(t['peak_rss_kib'] for t in trials) if all_exact and all(t.get('peak_rss_kib') is not None for t in trials) else None
            require(row['median_peak_rss_kib'][solver] == memory_median, 'memory median differs')
    publication = json.loads((folder / 'log_publication.json').read_text())
    published_paths = set()
    for entry in publication['files']:
        path = log_root / entry['path']
        require(sha(path) == entry['published_sha256'], 'published log identity differs')
        require(not re.search(r'/(?:workspace|opt/codex|root|home)/', path.read_text()), 'private execution path remains')
        published_paths.add(path.resolve())
    require(published_paths == {p.resolve() for p in (log_root / 'receipts/model_counting').rglob('*.log')}, 'publication log scope differs')
    fixtures = ROOT / 'data/model_counting/fixtures'
    originals = {r['name']: r for r in manifest['instances']}
    for fixture in fixtures.glob('*.cnf'):
        require(sha(fixture) == originals[fixture.name]['sha256'], 'original fixture bytes differ')
    return {'original_instances': 200, 'confirmed_native_cases_repeated': len(confirmed),
            'raw_result_logs_audited': audited_logs, 'exact_count_disagreements': 0}

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--log-root', type=Path, default=ROOT, help='root of the separately extracted detailed evidence archive')
    args = parser.parse_args()
    print(json.dumps(check(args.log_root), sort_keys=True))
