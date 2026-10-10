"""Build the offline exhibit and reproduce its exact answers and local timings."""
import argparse
import hashlib
import json
import platform
from pathlib import Path
from statistics import median
from time import perf_counter
from perfectpower.exact_showcase import build_results, query, matvec

ROOT = Path(__file__).resolve().parents[1]


def proof_binding():
    path = ROOT/'receipts/series_kernel/validation.json'
    receipt = json.loads(path.read_text())
    matches = all(hashlib.sha256((ROOT/p).read_bytes()).hexdigest() == digest
                  for p, digest in receipt['source_sha256'].items())
    if not matches or receipt['status'] != 'passed':
        raise ValueError('retained Lean evidence does not match current sources')
    return {'retained_status': receipt['status'], 'declaration_count': receipt['declaration_count'],
            'all_recorded_source_hashes_match': matches, 'recompiled_in_this_run': False,
            'receipt_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def enumeration(budget, rank):
    count, point, maximum = 0, None, None
    for y in range(budget//2, -1, -1):
        x = budget-2*y
        if count == rank:
            point = [str(x), str(y)]
        count += 1
        score = 3*x+5*y
        maximum = score if maximum is None else max(maximum, score)
    return {'count': str(count), 'point': point, 'maximum': str(maximum)}


def benchmark(results, repeats):
    cases = []
    for budget in (1000, 100000, 1000000, 10000000):
        rank = (budget//2+1)//3
        timings = {'enumeration': [], 'population_query': []}
        answers = {}
        for run in range(repeats):
            order = ['enumeration', 'population_query'] if run % 2 == 0 else ['population_query', 'enumeration']
            for method in order:
                start = perf_counter()
                result = enumeration(budget, rank) if method == 'enumeration' else query(budget, rank)
                timings[method].append(perf_counter()-start)
                answers[method] = {k: result[k] for k in ('count', 'point', 'maximum')}
        if answers['enumeration'] != answers['population_query']:
            raise AssertionError('benchmark answers differ')
        cases.append({'budget': budget, 'rank': rank, 'answer': answers['enumeration'],
                      'seconds': timings, 'median_seconds': {k: median(v) for k, v in timings.items()},
                      'enumerated_allocations': budget//2+1,
                      'population_query_includes': 'construction, count, select, reverse rank, endpoint optimization and independent elimination check'})
    large = []
    for _ in range(repeats):
        start = perf_counter(); answer = query()
        large.append(perf_counter()-start)
        if answer != results['population']:
            raise AssertionError('trillion-budget answer drift')
    source = results['machine']['source']
    reduced = results['machine']['transport']['reduced']
    steps = 4096
    machine_times = {'six_states': [], 'three_states': []}
    prefixes = {}
    for run in range(repeats):
        models = [('six_states', source), ('three_states', reduced)]
        if run % 2:
            models.reverse()
        for name, model in models:
            a = [[int(v) for v in row] for row in model['operators'][0]['matrix']]
            v = [int(x) for x in model['seed']]
            start = perf_counter(); prefix = []
            for _ in range(steps):
                prefix.append(v[0]); v = matvec(a, v)
            machine_times[name].append(perf_counter()-start); prefixes[name] = prefix
    if prefixes['six_states'] != prefixes['three_states'] or prefixes['three_states'] != [n//2+1 for n in range(steps)]:
        raise AssertionError('measured machine output differs')
    return {'schema': 'pp-exact-space-benchmark/1', 'python': platform.python_version(),
            'platform': platform.platform(), 'repeats': repeats, 'timer': 'perf_counter wall seconds',
            'population_cases': cases, 'trillion_budget_seconds': large,
            'trillion_budget_median_seconds': median(large),
            'machine': {'steps': steps, 'seconds': machine_times,
                        'median_seconds': {k: median(v) for k, v in machine_times.items()},
                        'dense_matrix_entries_per_step': {'six_states': 36, 'three_states': 9},
                        'all_outputs_equal': True, 'compilation_included': False},
            'scope': 'constructed local workloads; population timings include construction; machine timings cover iteration only; no industrial or universal solver claim'}


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, default=str)+'\n', encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'receipts/exact_space')
    parser.add_argument('--benchmark', action='store_true')
    parser.add_argument('--repeats', type=int, default=5)
    args = parser.parse_args()
    if not 1 <= args.repeats <= 20:
        parser.error('repeats must be 1 through 20')
    out = args.output; out.mkdir(parents=True, exist_ok=True)
    results = build_results(); results['evidence']['retained_lean'] = proof_binding()
    write_json(out/'results.json', results)
    measurements = benchmark(results, args.repeats) if args.benchmark else None
    if measurements:
        write_json(out/'benchmark.json', measurements)
    template = (ROOT/'web/exact-space/template.html').read_text(encoding='utf-8')
    payload = json.dumps({'results': results, 'benchmark': measurements}, default=str).replace('<', '\\u003c')
    (out/'index.html').write_text(template.replace('__SHOWCASE_DATA__', payload), encoding='utf-8')
    print(json.dumps({'status': 'passed', 'population': results['population'],
                      'retained_lean': results['evidence']['retained_lean'],
                      'benchmark': measurements is not None, 'output': str(out)}, indent=2))


if __name__ == '__main__':
    main()
