#!/usr/bin/env python3
"""Bounded reconstruction and receipt audit; NEVER runs the Petersen50 search.

Uses literal OR-Library case data, rebuilds missing depth-13 prefix accounting,
and checks retained claims. Prefix exact values remain historical assertions.
Optional --gates replays only Petersen28/39. No BFS checkpoint is manufactured.
"""
import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PAIRS = 'pairs=3,4;1,4;0,4;0,1;1,3;2,4'
COUNT = 702508860122761


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def prefix_accounting(path, directory):
    data = Path(path).read_bytes()
    require(len(data) >= 44 and data[:4] == b'PFX1', 'bad prefix header')
    n, m, depth, count = struct.unpack_from('<4I', data, 4)
    require((n, m, depth) == (50, 5, 13), 'unexpected prefix case/depth')
    require(len(data) == 44 + count * (20 + 2*m), 'prefix length/trailing bytes')
    exact, slo, shi = struct.unpack_from('<3Q', data, 20)
    records = []
    for k in range(count):
        off = 44 + k*(20 + 2*m)
        require(data[off:off+4] == bytes([depth, 0, 0, 0]), 'prefix depth/padding')
        lo, hi = struct.unpack_from('<2Q', data, off+4+2*m)
        require(0 <= lo < hi <= 1 << (n-depth), 'prefix bounds')
        records.append((lo, hi))
    require(sum(r[0] for r in records) == slo and sum(r[1] for r in records) == shi,
            'prefix sums disagree with header')
    solved, expansions = {}, 0
    for path in sorted(Path(directory).glob('results_w*.jsonl')):
        for line in path.read_text().splitlines():
            r = json.loads(line)
            idx = r['prefix']
            require(type(idx) is int and 0 <= idx < count, 'prefix receipt index')
            require(type(r.get('expansions')) is int and r['expansions'] >= 0,
                    'invalid expansion count')
            expansions += r['expansions']
            if 'exact' not in r:
                require(r.get('timeout') is True, 'unknown receipt')
                continue
            v = r['exact']
            require(type(v) is int and records[idx][0] <= v <= records[idx][1],
                    'recorded subtree count outside regenerated bounds')
            require(idx not in solved or solved[idx] == v, 'conflicting duplicates')
            solved[idx] = v
    lo, hi = exact+slo, exact+shi
    for idx, v in solved.items():
        lo += v-records[idx][0]
        hi += v-records[idx][1]
    groups = defaultdict(list)
    for idx, (lower, upper) in enumerate(records):
        groups[upper-lower].append(idx)
    # Historical qsort compares width only. Aggregate reconstruction must not
    # silently depend on an implementation-specific order within a tied group.
    touched_ties = [g for g in groups.values() if len(g)>1 and any(i in solved for i in g)]
    require(all(all(i in solved for i in g) for g in touched_ties),
            'partly solved width tie: original prefix identities required')
    return {'prefixes_total': count, 'prefixes_solved': len(solved),
            'split_exact': exact, 'interval': [lo, hi], 'width': hi-lo,
            'total_expansions': expansions, 'fully_solved_width_tie_groups': touched_ties,
            'aggregate_invariant_under_width_ties': True}



def recorded_final():
    result = json.loads((HERE/'petersen_50_result.json').read_text())
    bf = result['best_first_campaign']
    require((bf['n'], bf['m']) == (50, 5), 'result dimensions')
    require(bf['pairs'] == [[3,4],[1,4],[0,4],[0,1],[1,3],[2,4]], 'result pairs')
    require(bf['exact_accumulated'] == COUNT and bf['interval'] == [COUNT, COUNT]
            and bf['width'] == bf['heap_nodes'] == 0 and bf['closed_exactly'] is True,
            'recorded final accounting')
    require(result['exact_count'] == COUNT and result['combined_rigorous_interval'] == [COUNT, COUNT]
            and result['combined_width'] == 0 and result['closed_exactly'] is True,
            'combined final accounting')
    lines = (HERE/'bf50/bfseed_run.log').read_text().splitlines()
    final = re.fullmatch(r'RESULT completed=1 exact=(\d+) interval=\[(\d+), (\d+)\] width=0 expansions=(\d+) seconds=([\d.]+) peak_rss_kb=(\d+)', lines[-1])
    require(final is not None, 'missing/invalid closing log line')
    require(tuple(map(int, final.group(1,2,3,4))) == (COUNT,COUNT,COUNT,bf['expansions']),
            'closing log/JSON disagreement')
    prior = re.search(r'heap=(\d+).*width=(\d+)', lines[-2])
    require(prior is not None and int(prior[1]) > 0, 'missing final live progress sample')
    return {'recorded_exact_count': COUNT, 'recorded_expansions': bf['expansions'],
            'last_progress_heap': int(prior[1]), 'final_heap_zero_source': 'JSON assertion; RESULT completed=1',
            'checkpoint_present': (HERE/'bf50/state.bin').exists(),
            'checkpoint_recovered': False, 'exhaustive_search_replayed': False,
            'evidence_level': 'cross-checked historical assertions, not a search certificate'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--gates', action='store_true', help='also replay 28/39, never 50')
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    sys.path.insert(0, str(ROOT/'python'))
    from verify_planning_independent import original_cases
    cases = original_cases()
    report = {'schema': 'pp-compiled-repro-audit/1', 'final_record': recorded_final(),
              'raw_source_sha256': digest(ROOT/'data/planning/mknap1.txt'),
              'source_bound_cases': [], 'campaign_accounting': {}, 'gates': []}
    for n in (28,39,50):
        t = list(map(int, (HERE/f'petersen_{n}.txt').read_text().split()))
        nn,m=t[:2]; caps=t[2:2+m]; weights=[tuple(t[i:i+m]) for i in range(2+m,len(t),m)]
        raw, raw_caps, _, _ = cases[n]
        require(nn == n and caps == raw_caps and weights == raw, 'literal raw-case mismatch')
        require(n <= 50 and 1 <= m <= 16 and all(0 < c <= 65535 for c in caps)
                and all(0 <= x <= 65535-caps[j] for row in weights for j,x in enumerate(row)),
                'case exceeds audited native arithmetic domain')
        report['source_bound_cases'].append(n)
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp); binary=tmp/'petersen'
        build = subprocess.run(['gcc','-O3','-std=c11','-Wall','-Wextra',str(HERE/'petersen.c'),'-lm','-o',str(binary)],
                               check=True,capture_output=True,text=True,timeout=60)
        report['compiler'] = subprocess.check_output(['gcc','--version'], text=True).splitlines()[0]
        report['build_diagnostics'] = build.stderr
        def run(*words, timeout=60):
            r = subprocess.run([str(binary), *map(str,words)],capture_output=True,text=True,check=True,timeout=timeout)
            return r.stdout
        for name, pairs, expected in (
            ('campaign50', [], [677205149345632,708957902784392]),
            ('campaign50b', [PAIRS], [691091625831361,703631266985368])):
            prefix=tmp/f'{name}.bin'
            log=run('split',HERE/'petersen_50.txt',13,prefix,*pairs)
            accounting=prefix_accounting(prefix,HERE/name)
            require(accounting['interval'] == expected, 'historical partial interval mismatch')
            require(expected[0] <= COUNT <= expected[1], 'result outside partial interval')
            accounting.update(prefix_sha256=digest(prefix), reconstruction_log=log,
                              solved_counts_independently_recomputed=False)
            report['campaign_accounting'][name]=accounting
        if args.gates:
            for n,count,exps in ((28,208817578,1288947),(39,368072359571,136680243)):
                for pairs,exp in (([],exps),([PAIRS],921324 if n==28 else 8585148)):
                    log=run('dfs',HERE/f'petersen_{n}.txt',45,*pairs,timeout=60)
                    require(f'EXACT={count}\n' in log and f'expansions={exp} ' in log
                            and 'RESULT completed=1 ' in log, 'benchmark gate mismatch')
                    report['gates'].append({'case':n,'pairs':'six' if pairs else 'single','count':count,'expansions':exp,'log':log})
    audited = json.loads((HERE/'petersen_50_result.json').read_text())['python_campaign_audited_interval']
    require(audited == [699497138009147,703473996819983] and audited[0] <= COUNT <= audited[1], 'Python interval mismatch')
    report['python_interval_status']='retained historical interval, not replayed here'
    paths=[HERE/'petersen.c',HERE/'reproduce_evidence.py',HERE/'petersen_50_result.json',HERE/'bf50/bfseed_run.log']
    report['source_sha256']={str(p.relative_to(ROOT)):digest(p) for p in paths}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
