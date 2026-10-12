"""Standalone verification: raw OR-Library input -> ROBDDs; no planner imports.

Run from the repository: python python/verify_planning_independent.py --case 50
The original partition is used only as a conditional query bank AFTER building
the unrestricted diagram. It cannot influence the root count.
"""
import argparse
import hashlib
import itertools
import json
import platform
import random
import resource
import subprocess
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts/planning/independent'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def original_cases():
    tokens = iter((ROOT / 'data/planning/mknap1.txt').read_text().split())
    result = {}
    for _ in range(int(next(tokens))):
        n, m, best = int(next(tokens)), int(next(tokens)), next(tokens)
        profits = [next(tokens) for _ in range(n)]
        rows = [[int(next(tokens)) for _ in range(n)] for _ in range(m)]
        caps = [int(next(tokens)) for _ in range(m)]
        result[n] = (list(zip(*rows)), caps, profits, best)
    if list(tokens):
        raise ValueError('Trailing dataset tokens')
    return result


def partition_leaves(packet):
    n = packet['variables']
    splits, answers = {}, {}
    for row in packet['splits']:
        key = row['fixed'], row['values']
        if key in splits:
            raise ValueError('Duplicate split')
        splits[key] = row['bit']
    for row in packet['answers']:
        key = row['fixed'], row['values']
        if key in answers:
            raise ValueError('Duplicate answer')
        answers[key] = row['answer']
    visited = set()
    leaves = []

    def walk(fixed, values):
        key = fixed, values
        if key in visited or not 0 <= values <= fixed < 1 << n or values & ~fixed:
            raise ValueError('Invalid cube address')
        visited.add(key)
        if key in splits:
            bit = splits[key]
            if bit <= 0 or bit & (bit-1) or bit & fixed or bit >= 1 << n:
                raise ValueError('Invalid split coordinate')
            return walk(fixed | bit, values) + walk(fixed | bit, values | bit)
        answer = answers[key]
        if not 0 <= answer['count'] <= 1 << (n-fixed.bit_count()):
            raise ValueError('Impossible leaf count')
        leaves.append({'fixed': fixed, 'values': values, 'expected': answer['count']})
        return 1 << (n-fixed.bit_count())

    cover = walk(0, 0)
    if cover != 1 << n or not set(splits) <= visited:
        raise ValueError('Incomplete cover or unreachable splits')
    # Extra answers may belong to query banks. They are not root leaves.
    return leaves


def bdd_input(weights, caps, queries=()):
    n, m = len(weights), len(caps)
    order = sorted(range(n), key=lambda j: (-sum(weights[j]), j))

    def transport(mask):
        return sum(((mask >> (n-1-j)) & 1) << (n-1-i) for i, j in enumerate(order))

    text = f'{n} {m}\n' + ' '.join(map(str, caps)) + '\n'
    text += '\n'.join(' '.join(map(str, weights[j])) for j in order) + '\n'
    text += str(len(queries)) + '\n'
    text += '\n'.join(f'{transport(q["fixed"])} {transport(q["values"])}' for q in queries) + '\n'
    return text, order


def execute(binary, text, args, seconds=600, memory_mib=6144):
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (memory_mib*1024**2,)*2)
    start = time.perf_counter()
    try:
        run = subprocess.run([str(binary), *map(str, args)], input=text, text=True,
                             capture_output=True, timeout=seconds, preexec_fn=limits)
    except subprocess.TimeoutExpired as error:
        return {'status': 'timeout', 'wall_seconds': time.perf_counter()-start,
                'diagnostics': (error.stderr or b'').decode() if isinstance(error.stderr, bytes) else error.stderr}
    try:
        answer = json.loads(run.stdout)
    except ValueError:
        answer = {'status': 'process_failure', 'stdout': run.stdout}
    answer.update(exit_code=run.returncode, wall_seconds=time.perf_counter()-start,
                  diagnostics=run.stderr)
    return answer


def optimizer_input(weights, caps, profits, target):
    return (f'{len(weights)} {len(caps)} {target}\n' + ' '.join(map(str, caps)) + '\n' +
            '\n'.join(str(p)+' '+' '.join(map(str, w)) for p, w in zip(profits, weights))+'\n')


def compile_binaries(folder):
    result = {}
    for kind in ('bdd', 'optimizer'):
        source = ROOT / f'native/independent_planning_{kind}.cpp'
        binary = folder / kind
        command = ['g++', '-O3', '-std=c++17', str(source), '-o', str(binary)]
        subprocess.run(command, check=True, capture_output=True)
        result[kind] = binary
    return result


def selftest(binaries):
    rng = random.Random(20261012)
    for trial in range(80):
        n = rng.randrange(1, 11); m = rng.randrange(1, 6)
        weights = [[rng.randrange(8) for _ in range(m)] for _ in range(n)]
        caps = [rng.randrange(-1, 1+sum(w[k] for w in weights)) for k in range(m)]
        profits = [rng.randrange(10) for _ in range(n)]
        population = []
        for bits in itertools.product((0, 1), repeat=n):
            if all(sum(x*w[k] for x,w in zip(bits, weights)) <= caps[k] for k in range(m)):
                mask = sum(x << (n-1-j) for j, x in enumerate(bits))
                population.append((mask, sum(x*p for x,p in zip(bits, profits))))
        queries = []
        for _ in range(4):
            fixed = rng.randrange(1 << n); values = fixed & rng.randrange(1 << n)
            queries.append({'fixed': fixed, 'values': values})
        text, _ = bdd_input(weights, caps, queries)
        actual = execute(binaries['bdd'], text, [100000])
        assert actual['status'] == 'complete' and actual['count'] == len(population), (trial, actual)
        assert actual['conditional_counts'] == [sum(mask & q['fixed'] == q['values'] for mask,p in population) for q in queries]
        target = rng.randrange(1+sum(profits))
        actual = execute(binaries['optimizer'], optimizer_input(weights, caps, profits, target), [])
        candidates = [(mask,p) for mask,p in population if p >= target]
        best = max((p for mask,p in candidates), default=-1)
        maxima = [mask for mask,p in candidates if p == best]
        assert actual['candidates_at_or_above_target'] == len(candidates)
        assert (actual['maximum'], actual['maximizers'], actual['mask']) == (best, len(maxima), min(maxima, default=0))
    # Terminal truth, skipped coordinates, and the exact 2^62 count boundary.
    actual = execute(binaries['bdd'], bdd_input([[0]]*62, [0])[0], [100])
    assert actual['count'] == 1 << 62
    return {'random_exhaustive_cases': 80, 'conditional_queries': 320, 'count_boundary': 1 << 62}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--case', type=int, default=50)
    parser.add_argument('--nodes', type=int, default=40000000)
    parser.add_argument('--timeout', type=int, default=600)
    parser.add_argument('--memory-mib', type=int, default=6144)
    parser.add_argument('--selftest', action='store_true')
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as temporary:
        binaries = compile_binaries(Path(temporary))
        if args.selftest:
            result = selftest(binaries)
            (OUT/'validation.json').write_text(json.dumps(result, indent=2)+'\n')
            print(json.dumps(result)); return
        weights, caps, profit_text, target_text = original_cases()[args.case]
        profits, target = list(map(int, profit_text)), int(target_text)
        packet_path = ROOT/f'receipts/planning/population/{args.case}_partition.json'
        packet = json.loads(packet_path.read_text())
        assert packet['variables'] == args.case
        leaves = partition_leaves(packet)
        queries = list(leaves)
        if args.case == 50:
            for prefix in ('0'*26, '11111111111111101111010111', '00010101101110111011001011'):
                queries.append({'fixed': ((1 << len(prefix))-1) << (args.case-len(prefix)),
                                'values': int(prefix, 2) << (args.case-len(prefix)), 'prefix': prefix})
        text, order = bdd_input(weights, caps, queries)
        result = {'schema': 'pp-independent-planning/1', 'case': args.case,
                  'dataset_sha256': digest(ROOT/'data/planning/mknap1.txt'),
                  'partition_sha256': digest(packet_path),
                  'sources': {k: digest(ROOT/f'native/independent_planning_{k}.cpp') for k in binaries},
                  'driver_sha256': digest(Path(__file__)), 'compiler': subprocess.check_output(['g++','--version'], text=True).splitlines()[0],
                  'flags': ['-O3','-std=c++17'], 'platform': platform.platform(),
                  'limits': {'node_cap': args.nodes, 'timeout_seconds_per_worker': args.timeout, 'address_space_mib': args.memory_mib},
                  'order_original_indices': order, 'input_sha256': hashlib.sha256(text.encode()).hexdigest(),
                  'root_leaf_cubes': len(leaves), 'cube_cover_size': 1 << args.case,
                  'independence': 'Standalone original-data parser, threshold ROBDD construction and Boolean intersection; partition used only for post-construction queries. No planner/native kernel imports.'}
        result['optimizer'] = execute(binaries['optimizer'], optimizer_input(weights,caps,profits,target), [], args.timeout, args.memory_mib)
        result['bdd'] = execute(binaries['bdd'], text, [args.nodes], args.timeout, args.memory_mib)
        if result['bdd']['status'] == 'complete':
            answers = result['bdd']['conditional_counts']
            assert len(answers) == len(queries)
            result['conditional_results'] = [dict(q, independent_count=c) for q,c in zip(queries,answers)]
            result['all_root_leaf_counts_agree'] = all(q['expected'] == c for q,c in zip(leaves,answers))
            result['independent_leaf_sum'] = sum(answers[:len(leaves)])
            assert result['independent_leaf_sum'] == result['bdd']['count']
            # Comparison occurs only after unrestricted independent computation.
            published = json.loads((ROOT/f'receipts/planning/population/{args.case}_population.json').read_text())
            result['published_root_agrees'] = published['count'] == result['bdd']['count']
            result['status'] = 'complete_independent_confirmation' if result['all_root_leaf_counts_agree'] and result['published_root_agrees'] else 'disagreement'
        else:
            result['status'] = 'incomplete_full_count'
        result['direct_conditional_rebuilds'] = []
        for q in queries[len(leaves):]:
            prefix = list(map(int, q['prefix']))
            remaining_caps = [b-sum(x*w[k] for x,w in zip(prefix,weights)) for k,b in enumerate(caps)]
            direct_text, _ = bdd_input(weights[len(prefix):], remaining_caps)
            direct = execute(binaries['bdd'], direct_text, [args.nodes], args.timeout, args.memory_mib)
            result['direct_conditional_rebuilds'].append({'prefix': q['prefix'], 'answer': direct})
            if result['bdd']['status'] == 'complete':
                assert direct['status'] == 'complete' and direct['count'] == answers[queries.index(q)]
        opt = result['optimizer']
        if opt['status'] == 'complete' and opt['candidates_at_or_above_target']:
            bits = [(opt['mask'] >> (args.case-1-j)) & 1 for j in range(args.case)]
            used = [sum(x*w[k] for x,w in zip(bits,weights)) for k in range(len(caps))]
            assert all(u <= b for u,b in zip(used,caps))
            assert sum(x*p for x,p in zip(bits,profits)) == opt['maximum']
            result['optimizer_witness'] = {'original_bits': bits, 'resource_use': used}
        path = OUT/f'{args.case}_bdd_nodes{args.nodes}.json'
        path.write_text(json.dumps(result, indent=2)+'\n')
        print(json.dumps({'receipt': str(path), 'status': result['status'], 'bdd': result['bdd'], 'optimizer': result['optimizer']}))


if __name__ == '__main__':
    main()
