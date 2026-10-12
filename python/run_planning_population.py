"""Isolated, bounded population comparisons; optimizer results stay separate."""
import argparse
from copy import deepcopy
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import resource
import subprocess
import sys
from time import perf_counter
from perfectpower.planning import CompletionPlanner, optimize_allocation
from perfectpower.planning_native import NativeIndex, library, recursive_reference
from perfectpower.planning_cnf import encode_allocation
from perfectpower.divisor_square import WorkLimit
from run_planning import parse_public, GrayIndex, ortools_optimum

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'receipts/planning/population'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix('.tmp')
    tmp.write_text(json.dumps(data, indent=2)+'\n')
    tmp.replace(path)

def bank(p):
    total = p.count()
    records = []
    for rank in sorted({0, total//4, total//2, 3*total//4, total-1}):
        point = p.select(rank)
        if hasattr(p, 'selected_ranks'):
            p.selected_ranks.clear()
        reverse = p.rank(point)
        assert reverse == rank
        records.append({'rank': rank, 'point': point, 'inverse_rank': reverse,
                        'prefix_count': p.completions(point[:3])['count']})
    optimum = p.optimize()
    if hasattr(p, 'selected_ranks'):
        point = p.select(0, optimal=True)
        p.selected_ranks.clear()
        assert p.rank(point, optimal=True) == 0
        assert point == optimum['point']
        assert p.completions(point)['count'] == 1
    return {'count': total, 'optimization': optimum, 'bank': records}

def check_partition(packet, root_answer):
    """Check the finite disjoint cover and recompute every internal aggregate."""
    n = packet['variables']
    splits = {(r['fixed'], r['values']): r['bit'] for r in packet['splits']}
    answers = {(r['fixed'], r['values']): r['answer'] for r in packet['answers']}
    leaves = []
    def visit(fixed, values):
        assert values & ~fixed == 0 and fixed < 1 << n
        key = (fixed, values)
        if key not in splits:
            a = answers[key]
            assert 0 <= a['count'] <= 1 << (n-fixed.bit_count())
            leaves.append(key)
            return a
        bit = splits[key]
        assert bit > 0 and bit & (bit-1) == 0 and not bit & fixed and bit < 1 << n
        a = visit(fixed|bit, values)
        b = visit(fixed|bit, values|bit)
        count = a['count']+b['count']
        best = max(r['best'] for r in (a, b) if r['count']) if count else 0
        ties = sum(r['ties'] for r in (a, b) if r['count'] and r['best'] == best)
        masks = [r['mask'] for r in (a, b) if r['count'] and r['best'] == best]
        combined = {'count': count, 'best': best, 'ties': ties, 'mask': min(masks) if masks else 0}
        if key in answers:
            assert all(answers[key][k] == combined[k] for k in combined)
        return combined
    a = visit(0, 0)
    assert all(a[k] == root_answer[k] for k in ('count', 'best', 'ties', 'mask'))
    assert sum(1 << (n-f.bit_count()) for f, v in leaves) == 1 << n
    return {'root_leaves': len(leaves), 'disjoint_cover_size': 1 << n,
            'root': {k: a[k] for k in ('count', 'best', 'ties', 'mask')},
            'scope': 'cover and arithmetic replay; native leaf computations require their own validation'}

def independent_prefixes(p, spec, points):
    results = []
    n = len(spec['variables'])
    for point in points:
        prefix = point[:max(0, n-24)]
        used = [sum(x*v['costs'][k] for x, v in zip(prefix, spec['variables'])) for k in range(len(spec['resources']))]
        suffix = deepcopy(spec)
        suffix['resources'] = [dict(r, min=max(0, r.get('min', 0)-u), max=r['max']-u) for r, u in zip(spec['resources'], used)]
        suffix['variables'] = spec['variables'][len(prefix):]
        start = perf_counter()
        ref, scale = recursive_reference(CompletionPlanner(suffix, _compile=False))
        actual = p.completions(prefix)
        score = sum(Fraction(v['profit'])*x for x, v in zip(prefix, spec['variables']))
        assert actual['count'] == ref['count'] and actual['maximizer_count'] == ref['ties']
        assert Fraction(actual['maximum']) == score+Fraction(ref['best'], scale)
        for bit in (0, 1):
            child = p.completions(prefix+[bit])
            results.append({'prefix': prefix+[bit], 'count': child['count']})
        assert actual['count'] == sum(r['count'] for r in results[-2:])
        results.append({'prefix': prefix, 'count': actual['count'], 'reference': ref,
                        'reference_seconds': perf_counter()-start, 'scope': 'independent original-order subcube recursion, without polynomials, implication tables or memoization'})
    return results

def worker(args):
    spec = next(r['specification'] for r in parse_public() if len(r['specification']['variables']) == args.case)
    out = OUT/f'{args.case}_{args.variant}.json'
    result = {'schema': 'pp-population-benchmark/1', 'case': args.case, 'variant': args.variant,
              'python': platform.python_version(), 'platform': platform.platform(),
              'cpu': next((line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')), None),
              'dataset_sha256': digest(ROOT/'data/planning/mknap1.txt'),
              'native_source_sha256': digest(ROOT/'native/completion_planner.cpp'),
              'memory_scope': 'fresh worker Linux peak RSS, interpreter and loaded library included; compiler child excluded',
              'limits': {'arena_bytes': args.memory_mib*1024**2, 'memo_states': args.states,
                         'per_call_work': args.call_work, 'per_query_work': args.total_work, 'partition_nodes': 8192}}
    spec = dict(spec, population_memory_limit=args.memory_mib*1024**2, population_cache_states=args.states,
                native_visit_limit=args.call_work, population_work_limit=args.total_work)
    start = perf_counter()
    lib = library()
    result['compile_load_seconds'] = perf_counter()-start
    result['compiler'] = lib._provenance
    save(out, result)
    try:
        t = perf_counter()
        if args.variant in ('population', 'mitm', 'python_dp'):
            p = CompletionPlanner(dict(spec, strategy={'python_dp': 'dp'}.get(args.variant, args.variant)))
        elif args.variant == 'native_exhaustive':
            p = CompletionPlanner(dict(spec, strategy='mitm'), _compile=False)
            p.index = NativeIndex(p, exhaustive=True)
            p.root_entry = p._indexed_entry(())
        elif args.variant == 'gray':
            p = GrayIndex(spec)
        elif args.variant == 'optimization':
            result['optimization_only'] = optimize_allocation(spec)
            result['optimization_only_seconds'] = perf_counter()-t
            result['status'] = 'complete_optimization_only'
            return save(out, result)
        elif args.variant == 'ortools':
            result['optimization_only'] = ortools_optimum(spec)
            result['optimization_only_seconds'] = perf_counter()-t
            result['status'] = 'complete_optimization_only'
            return save(out, result)
        result['cold_population_seconds'] = perf_counter()-t
        result['status'] = 'complete_population'
        result['count'] = p.count()
        if args.variant == 'population':
            result['root_answer'] = p.index.query(())
            packet = p.index.partition_receipt()
            result['partition_validation'] = check_partition(packet, result['root_answer'])
            save(OUT/f'{args.case}_partition.json', packet)
        save(out, result)
        print('population', args.case, p.count(), result['cold_population_seconds'], flush=True)
        t = perf_counter()
        result['answers'] = bank(p)
        result['first_query_bank_seconds'] = perf_counter()-t
        t = perf_counter()
        for _ in range(20):
            assert bank(p) == result['answers']
        result['cached_sustained_bank_seconds'] = (perf_counter()-t)/20
        result['warm_scope'] = '20 repetitions of the retained five-rank bank; inverse ranks recomputed; conditional results reused'
        if args.variant == 'population':
            result['independent_prefix_checks'] = independent_prefixes(p, spec, [r['point'] for r in result['answers']['bank']])
            result['post_query_partition_nodes'] = len(p.index.fixed_cache)+len(p.index.partitions)
            result['total_search_visits'] = p.index.query_visits
            result['total_setup_cells'] = p.index.setup_cells
            # Verify branch count identities away from selected complete witnesses.
            branches = []
            for prefix in ([], [0], [1], [0, 1], [1, 0]):
                a, b, c = (p.completions(prefix+x)['count'] for x in ([], [0], [1]))
                assert a == b+c
                branches.append({'prefix': prefix, 'parent': a, 'zero': b, 'one': c})
            result['branch_identities'] = branches
            result['sample'] = p.sample(random.Random(20261012))
            assert p.completions(result['sample'])['count'] == 1
        result['status'] = 'complete_workflow'
    except WorkLimit as e:
        result['status'] = 'WORK_LIMIT'
        result['reason'] = str(e)
        result['details'] = getattr(e, 'details', {})
    finally:
        result['worker_seconds'] = perf_counter()-start
        result['peak_rss_bytes'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024
        save(out, result)
    print(result['status'], args.case, args.variant, flush=True)

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--case', type=int, choices=[6, 10, 15, 20, 28, 39, 50], required=True)
    ap.add_argument('--variant', choices=['population', 'mitm', 'gray', 'native_exhaustive', 'python_dp', 'optimization', 'ortools'], default='population')
    ap.add_argument('--memory-mib', type=int, default=128)
    ap.add_argument('--states', type=int, default=1000000)
    ap.add_argument('--call-work', type=int, default=10000000)
    ap.add_argument('--total-work', type=int, default=2000000000)
    args = ap.parse_args()
    if not 1 <= args.memory_mib <= 1024 or not 0 <= args.states <= 8000000:
        ap.error('memory/state limits out of range')
    worker(args)
