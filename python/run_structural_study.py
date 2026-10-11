#!/usr/bin/env python3
"""Run the complete declared structural study serially, with durable receipts.

Use a fresh output prefix and private evidence directory. The comparator owns
the shared process lock and rejects source changes or overwritten receipts.
This driver never substitutes longer-budget outcomes for primary failures.
"""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--mc2025', type=Path, required=True)
    p.add_argument('--mc2024', type=Path, required=True)
    p.add_argument('--previous-root', type=Path, required=True)
    p.add_argument('--ganak', type=Path, required=True)
    p.add_argument('--d4', type=Path, required=True)
    p.add_argument('--evidence', type=Path, required=True)
    p.add_argument('--prefix', default='structural')
    a = p.parse_args()
    if not a.prefix or any(c not in 'abcdefghijklmnopqrstuvwxyz0123456789_-' for c in a.prefix):
        p.error('portable lowercase output prefix required')
    receipts = ROOT / 'receipts/model_counting'
    a.evidence.mkdir(parents=True, exist_ok=True)
    protocol = ROOT / 'docs/MODEL_COUNTING_STRUCTURAL_PROTOCOL.md'
    frozen = {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
              for path in [protocol, Path(__file__).resolve(),
                           ROOT / 'python/ablate_structural_counting.py']}

    def execute(script, args):
        if any(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != sha
               for name, sha in frozen.items()):
            raise RuntimeError('study protocol or driver changed')
        subprocess.run([sys.executable, str(ROOT / 'python' / script), *map(str, args)],
                       cwd=ROOT, check=True)

    def compare(label, year, *, names=None, timeout=5, repetitions=1, references=False):
        output = receipts / f'{a.prefix}_{label}.json'
        args = ['--manifest', ROOT / 'data/model_counting' /
                ('mc2025_manifest.json' if year == 2025 else 'manifest.json'),
                '--corpus', a.mc2025 if year == 2025 else a.mc2024,
                '--previous-root', a.previous_root, '--timeout', timeout,
                '--memory-gib', 6, '--repetitions', repetitions,
                '--output', output, '--log-directory', a.evidence / label]
        if names:
            args += ['--names', *names]
        if references:
            args += ['--ganak', a.ganak, '--d4', a.d4]
        execute('compare_model_counting.py', args)
        execute('analyze_model_counting_comparison.py',
                [output, '--output', receipts / f'{a.prefix}_{label}_analysis.json'])
        return json.loads(output.read_text())

    identity = receipts / f'{a.prefix}_protocol.json'
    if identity.exists():
        raise RuntimeError('fresh study prefix required')
    identity.write_text(json.dumps({'schema': 'pp-cnf-study-protocol/1',
                                  'frozen_sources': frozen,
                                  'baseline_commit': 'd4dc8dc6fa5ba5f6c6f11e81ccd766e1d3bdf3cc',
                                  'primary_timeout_seconds': 5,
                                  'memory_gib': 6,
                                  'corpus_scope': 'Known development corpora, not blind holdouts'},
                                 indent=2) + '\n')
    new = compare('mc2025', 2025, references=True)
    old = compare('mc2024', 2024)
    for year, screen in [(2025, new), (2024, old)]:
        names = sorted({r['name'] for r in screen['results']
                        if any(r['solvers'][s]['status'] == 'EXACT'
                               for s in ('perfectpower', 'previous'))})
        if names:
            compare(f'mc{year}_repeated', year, names=names, repetitions=3,
                    references=(year == 2025))
    historical = json.loads((receipts / 'next_mc2025.json').read_text())
    legacy = sorted({r['name'] for r in historical['results']
                     if r['solvers']['perfectpower']['status'] == 'EXACT'})
    legacy_report = compare('legacy_repeated', 2025, names=legacy,
                            timeout=15, repetitions=3)
    unconfirmed = set()
    confirmed = {r['name'] for r in new['results']
                 if any(r['solvers'][s]['status'] == 'EXACT' for s in ('ganak', 'd4_2024'))}
    for screen in (new, legacy_report):
        unconfirmed.update(r['name'] for r in screen['results']
                           if r['solvers']['perfectpower']['status'] == 'EXACT'
                           and r['name'] not in confirmed)
    if unconfirmed:
        compare('reference_validation', 2025, names=sorted(unconfirmed),
                timeout=30, repetitions=3, references=True)
    solved = {r['name'] for r in new['results'] if r['solvers']['perfectpower']['status'] == 'EXACT'}
    gained = set(new['summary']['paired_change']['gained'])
    selected = sorted((gained | {'mc2025_track1_025.cnf', 'mc2025_track1_042.cnf',
                                'mc2025_track1_074.cnf'}) & solved)
    if selected:
        execute('ablate_structural_counting.py',
                ['--previous-root', a.previous_root,
                 '--screen', receipts / f'{a.prefix}_mc2025.json',
                 '--corpus', a.mc2025, '--names', *selected,
                 '--output', receipts / f'{a.prefix}_ablation.json',
                 '--work-directory', a.evidence / 'ablation',
                 '--timeout', 10, '--repetitions', 3])
    execute('analyze_model_counting_overlap.py',
            ['--receipt', receipts / f'{a.prefix}_mc2025.json',
             '--overlap', receipts / 'next_overlap.json',
             '--output', receipts / f'{a.prefix}_overlap_analysis.json'])
    print('All declared structural study phases completed.', flush=True)


if __name__ == '__main__':
    main()
