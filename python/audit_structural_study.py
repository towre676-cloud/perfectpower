#!/usr/bin/env python3
"""Audit completed structural receipts and their privately retained raw logs."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_from_log(path):
    stdout = path.read_text().split('\n--- STDERR ---\n', 1)[0].strip()
    counts = re.findall(r'^c s exact arb int ([0-9]+)\s*$', stdout, re.M)
    if not counts:
        counts = re.findall(r'^s (?:mc )?([0-9]+)\s*$', stdout, re.M)
    if counts:
        return counts[-1]
    answer = json.loads(stdout)
    if answer['status'] != 'EXACT':
        raise ValueError('receipt says exact but log does not')
    return answer['count']


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--evidence', type=Path, required=True)
    p.add_argument('--previous-root', type=Path, required=True)
    p.add_argument('--prefix', default='structural')
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    directory = ROOT / 'receipts/model_counting'
    paths = sorted(directory.glob(a.prefix + '_*.json'))
    primary = {directory / f'{a.prefix}_mc2025.json', directory / f'{a.prefix}_mc2024.json'}
    if not primary.issubset(set(paths)):
        raise ValueError('both full screens required')
    protocol = json.loads((directory / f'{a.prefix}_protocol.json').read_text())
    for name, expected_sha in protocol['frozen_sources'].items():
        if sha(ROOT / name) != expected_sha:
            raise ValueError('study protocol identity mismatch')
    correctness = json.loads((directory / f'{a.prefix}_correctness.json').read_text())
    for key, name in [('counter_sha256', 'native/model_counting/counter.cpp'),
                      ('native_harness_sha256', 'native/model_counting/test_exhaustive.cpp'),
                      ('python_test_sha256', 'python/tests/test_model_counting.py')]:
        if correctness[key] != sha(ROOT / name):
            raise ValueError('correctness source identity mismatch')
    if correctness['native_result_log_sha256'] != sha(a.evidence / 'correctness/sanitizer.log'):
        raise ValueError('sanitizer result identity mismatch')
    source_paths = {
        'counter': ROOT / 'native/model_counting/counter.cpp',
        'python': ROOT / 'python/perfectpower/model_counting.py',
        'runner': ROOT / 'python/compare_model_counting.py',
        'execution': ROOT / 'python/run_model_counting.py',
        'previous_counter': a.previous_root / 'native/model_counting/counter.cpp',
        'previous_python': a.previous_root / 'python/perfectpower/model_counting.py',
        'previous_worker': a.previous_root / 'python/run_model_counting.py',
    }
    reports = []
    verified_counts = {}
    reference_counts = {}
    current_counts = {}
    references = json.loads((ROOT / 'data/model_counting/references.json').read_text())
    for path in paths:
        receipt = json.loads(path.read_text())
        schema = receipt.get('schema')
        if schema not in ('pp-cnf-paired/1', 'pp-cnf-ablation/1'):
            continue
        if not receipt['completed']:
            raise ValueError('incomplete receipt: ' + path.name)
        label = path.stem[len(a.prefix) + 1:]
        identities = receipt.get('source_identities', {})
        if schema == 'pp-cnf-paired/1':
            for solver, key in [('ganak', 'ganak_binary'), ('d4_2024', 'd4_binary')]:
                if solver in receipt['solver_scope'] and identities[key] != references[
                        'ganak' if solver == 'ganak' else 'd4']['binary_sha256']:
                    raise ValueError('reference identity mismatch')
            for key, file in source_paths.items():
                if identities[key] != sha(file):
                    raise ValueError('source mismatch: ' + key)
            manifest_path = ROOT / 'data/model_counting' / (
                'mc2025_manifest.json' if '2025' in receipt['dataset'].upper()
                else 'manifest.json')
            if identities['manifest'] != sha(manifest_path):
                raise ValueError('manifest mismatch')
            manifest = json.loads(manifest_path.read_text())
            corpus_hashes = {r['name']: r['sha256'] for r in manifest['instances']}
            if path in primary and (len(receipt['instances']) != 200 or
                                    set(receipt['instances']) != set(corpus_hashes)):
                raise ValueError('incomplete primary scope')
            if len(receipt['results']) != len(receipt['instances']) * receipt['repetitions']:
                raise ValueError('incomplete rows')
            observed = set()
            for row in receipt['results']:
                key = (row['name'], row['trial'])
                if key in observed or row['name'] not in receipt['instances'] or not 0 <= row['trial'] < receipt['repetitions']:
                    raise ValueError('invalid or duplicate trial')
                observed.add(key)
                if row['sha256'] != corpus_hashes[row['name']]:
                    raise ValueError('input identity mismatch')
                if set(row['solvers']) != set(receipt['solver_scope']):
                    raise ValueError('missing solver')
                for solver, result in row['solvers'].items():
                    if Path(result['log']).name != result['log']:
                        raise ValueError('nonportable log name')
                    log = a.evidence / label / result['log']
                    if sha(log) != result['log_sha256']:
                        raise ValueError('log hash mismatch')
                    if result['status'] == 'EXACT':
                        if exact_from_log(log) != result['count']:
                            raise ValueError('log count mismatch')
                        target = current_counts if solver == 'perfectpower' else verified_counts
                        target.setdefault(row['sha256'], set()).add(result['count'])
                        if solver not in ('perfectpower', 'previous'):
                            reference_counts.setdefault(row['sha256'], set()).add(result['count'])
                counts = {o['count'] for o in row['solvers'].values() if o['status'] == 'EXACT'}
                if len(counts) > 1:
                    raise ValueError('exact disagreement')
        else:
            if receipt['native_source_sha256'] != sha(source_paths['counter']):
                raise ValueError('ablation source mismatch')
            candidates = [p for p in paths if sha(p) == receipt['screen_sha256']]
            if len(candidates) != 1:
                raise ValueError('ablation selection screen mismatch')
            screen_path = candidates[0]
            expected = {r['name']: r['solvers']['perfectpower']['count']
                        for r in json.loads(screen_path.read_text())['results']
                        if r['solvers']['perfectpower']['status'] == 'EXACT'}
            from ablate_structural_counting import variants
            sources = variants(source_paths['counter'].read_text(), source_paths['previous_counter'].read_text())
            for variant, source in sources.items():
                root = a.evidence / label / variant
                if receipt['variant_source_sha256'][variant] != hashlib.sha256(source.encode()).hexdigest():
                    raise ValueError('variant identity mismatch')
                if (root / 'native/model_counting/counter.cpp').read_text() != source:
                    raise ValueError('variant source mismatch')
            if len(receipt['results']) != len(receipt['instances']) * receipt['repetitions']:
                raise ValueError('incomplete ablation')
            for row in receipt['results']:
                for result in row['variants'].values():
                    if Path(result['log']).name != result['log']:
                        raise ValueError('nonportable ablation log name')
                    log = a.evidence / label / 'logs' / result['log']
                    if sha(log) != result['log_sha256']:
                        raise ValueError('ablation log mismatch')
                    if result['status'] == 'EXACT' and exact_from_log(log) != result['count']:
                        raise ValueError('ablation count mismatch')
                    if result['status'] == 'EXACT' and result['count'] != expected[row['name']]:
                        raise ValueError('ablation differs from selection screen')
        reports.append({'receipt': path.name, 'sha256': sha(path),
                        'rows': len(receipt['results']),
                        'logs': sum(len(r.get('solvers', r.get('variants', {}))) for r in receipt['results'])})
    for key, values in current_counts.items():
        if len(values | verified_counts.get(key, set())) > 1:
            raise ValueError('cross-receipt count disagreement')
    a.output.write_text(json.dumps({'schema': 'pp-cnf-structural-audit/1',
                                   'audit_source_sha256': sha(Path(__file__).resolve()),
                                   'receipts': reports,
                                   'log_count': sum(r['logs'] for r in reports),
                                   'current_exact_input_hashes': len(current_counts),
                                   'paired_or_reference_confirmed_input_hashes': sum(k in verified_counts for k in current_counts),
                                   'fresh_reference_confirmed_input_hashes': sum(k in reference_counts for k in current_counts),
                                   'count_disagreements': 0}, indent=2) + '\n')


if __name__ == '__main__':
    main()
