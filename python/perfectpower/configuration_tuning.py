"""Measured application objectives over bounded exact candidate populations."""
from random import Random
from statistics import median
from time import perf_counter_ns
import platform


def tune(population, run, expected, *, repeats=5, warmups=1, candidate_limit=64, seed=0, clock=perf_counter_ns):
    """Interleave all candidates; check every result against a supplied reference.

    `run` is a Python callable, never source evaluated by the service. The
    optimum is a measured median over these candidates and this workload.
    """
    if type(candidate_limit) is not int or not 1 <= candidate_limit <= 1024:
        raise ValueError('candidate limit 1 through 1024 required')
    if not 1 <= population.cardinality <= candidate_limit:
        raise ValueError('nonempty population must fit candidate budget')
    if type(repeats) is not int or not 1 <= repeats <= 100 or type(warmups) is not int or not 0 <= warmups <= 10:
        raise ValueError('repeats 1..100 and warmups 0..10 required')
    records = [population.select(i) for i in range(population.cardinality)]
    times = [[] for _ in records]; ledger = []; random = Random(seed)
    for round_index in range(-warmups, repeats):
        order = list(range(len(records))); random.shuffle(order)
        for rank in order:
            start = clock(); actual = run(records[rank]['values']); elapsed = clock()-start
            if actual != expected:
                raise ValueError(f'kernel result differs from independent reference at rank {rank}')
            if elapsed < 0:
                raise ValueError('clock must be monotone')
            if round_index >= 0:
                times[rank].append(elapsed)
                ledger.append(dict(round=round_index, rank=rank, elapsed_ns=elapsed))
    scores = [dict(record=r, median_ns=median(t), min_ns=min(t), max_ns=max(t), trials_ns=t)
              for r, t in zip(records, times)]
    best = min(x['median_ns'] for x in scores)
    return dict(schema='pp-measured-tuning/1', population_id=population.population_id,
                candidates=scores, winners=[x['record'] for x in scores if x['median_ns'] == best],
                minimum_median_ns=best, ledger=ledger, repeats=repeats, warmups=warmups, seed=seed,
                environment=dict(python=platform.python_version(), machine=platform.machine(), system=platform.system()),
                scope='minimum measured median among all supplied candidates on this host/workload; no universal speedup claim')


def blocked_matmul(left, right, row_block, column_block):
    """Real exact integer matrix kernel with compatible two-axis tile sizes."""
    if type(row_block) is not int or type(column_block) is not int or min(row_block, column_block) < 1:
        raise ValueError('positive integer block sizes required')
    n = len(left); k = len(right); m = len(right[0]) if k else 0
    if not n or not k or not m or any(len(r) != k for r in left) or any(len(r) != m for r in right):
        raise ValueError('nonempty rectangular compatible matrices required')
    out = [[0]*m for _ in range(n)]
    for a in range(0, n, row_block):
        for b in range(0, m, column_block):
            for i in range(a, min(n, a+row_block)):
                for t in range(k):
                    v = left[i][t]
                    for j in range(b, min(m, b+column_block)):
                        out[i][j] += v*right[t][j]
    return out
