#!/usr/bin/env python3
"""Paired, instance-clustered descriptive analysis; no selected-case ranking."""
import argparse
import hashlib
import json
import math
import random
import statistics
from pathlib import Path


def analyze(receipt, baseline, bootstraps=5000, seed=4269):
    if not receipt.get('completed'):
        raise ValueError('complete receipt required')
    if baseline == 'perfectpower' or baseline not in receipt['solver_scope']:
        raise ValueError('independent declared baseline required')
    timeout = receipt['timeout_seconds']
    clusters = []
    cases = []
    for name in receipt['instances']:
        rows = [r for r in receipt['results'] if r['name'] == name]
        if len(rows) != receipt['repetitions']:
            raise ValueError('incomplete instance cluster')
        current = [r['solvers']['perfectpower'] for r in rows]
        prior = [r['solvers'][baseline] for r in rows]
        solved_current = all(o['status'] == 'EXACT' for o in current)
        solved_prior = all(o['status'] == 'EXACT' for o in prior)
        cost_current = statistics.mean(o['seconds'] if o['status'] == 'EXACT' else 2*timeout for o in current)
        cost_prior = statistics.mean(o['seconds'] if o['status'] == 'EXACT' else 2*timeout for o in prior)
        log_ratio = None
        if solved_current and solved_prior:
            counts = {o['count'] for o in current + prior}
            if len(counts) != 1:
                raise ValueError('count disagreement')
            log_ratio = math.log(statistics.median(o['seconds'] for o in prior)
                                 / statistics.median(o['seconds'] for o in current))
        clusters.append((int(solved_current)-int(solved_prior), cost_prior-cost_current, log_ratio))
        cases.append({'name': name, 'current_exact_all_trials': solved_current,
                      'baseline_exact_all_trials': solved_prior,
                      'median_speedup': math.exp(log_ratio) if log_ratio is not None else None})
    if not clusters or bootstraps < 100:
        raise ValueError('nonempty scope and at least 100 resamples required')
    rng = random.Random(seed)
    sampled = [[], [], []]
    for _ in range(bootstraps):
        batch = [rng.choice(clusters) for _ in clusters]
        sampled[0].append(sum(c[0] for c in batch))
        sampled[1].append(sum(c[1] for c in batch))
        ratios = [c[2] for c in batch if c[2] is not None]
        if ratios:
            sampled[2].append(math.exp(statistics.mean(ratios)))

    def interval(values):
        if not values:
            return None
        values = sorted(values)
        return [values[int(.025*(len(values)-1))], values[int(.975*(len(values)-1))]]

    ratios = [c[2] for c in clusters if c[2] is not None]
    return {
        'baseline': baseline, 'instances': len(clusters), 'seed': seed,
        'bootstrap_resamples': bootstraps,
        'method': 'Paired empirical instance-cluster percentile bootstrap; all repeated trials of an instance stay together; descriptive uncertainty over this corpus, not proof of out-of-distribution performance',
        'coverage_delta': sum(c[0] for c in clusters),
        'coverage_delta_95_percent_interval': interval(sampled[0]),
        'par2_seconds_saved': sum(c[1] for c in clusters),
        'par2_saved_95_percent_interval': interval(sampled[1]),
        'jointly_solved_instances': len(ratios),
        'jointly_solved_geometric_speedup': math.exp(statistics.mean(ratios)) if ratios else None,
        'jointly_solved_speedup_95_percent_interval': interval(sampled[2]),
        'speedup_bootstrap_defined_resamples': len(sampled[2]),
        'speedup_scope_warning': 'Conditional on both solvers finishing every trial; timeout and unsupported cases are excluded only from this speed ratio, never from coverage or PAR-2',
        'cases': cases,
    }


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('receipt', type=Path);p.add_argument('--output', type=Path, required=True)
    args = p.parse_args();raw = args.receipt.read_bytes();receipt = json.loads(raw)
    report = {'schema': 'pp-cnf-paired-analysis/1',
              'receipt_sha256': hashlib.sha256(raw).hexdigest(),
              'analysis_source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'comparisons': [analyze(receipt, s) for s in receipt['solver_scope'] if s != 'perfectpower']}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
