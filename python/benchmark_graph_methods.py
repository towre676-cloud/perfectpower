"""Reproducible structured and adverse trials against an independent cached DPLL.

This baseline is internal, not Ganak, D4, or the industrial SMT benchmark.
"""
import json
import platform
import random
import statistics
import time
from functools import lru_cache
from pathlib import Path
from perfectpower.graph_counting import count_cnf
from perfectpower.divisor_square import WorkLimit


def reference_count(n, clauses):
    """Cached DPLL with unit propagation, independently written from factor tables."""
    normalized=tuple(sorted({tuple(sorted(set(c))) for c in clauses if not any(-l in c for l in c)}))
    @lru_cache(None)
    def solve(active,formula):
        active=set(active)
        while True:
            if () in formula:return 0
            if not formula:return 2**len(active)
            units={c[0] for c in formula if len(c)==1}
            if not units:break
            if any(-l in units for l in units):return 0
            active.difference_update(abs(l) for l in units)
            formula=tuple(sorted({tuple(l for l in c if -l not in units) for c in formula if not any(l in units for l in c)}))
        v=abs(min(formula,key=len)[0]);remaining=tuple(sorted(active-{v}))
        def branch(l):return tuple(sorted({tuple(x for x in c if x!=-l) for c in formula if l not in c}))
        return solve(remaining,branch(v))+solve(remaining,branch(-v))
    return solve(tuple(range(1,n+1)),normalized)


def main():
    r=random.Random(20261011);cases=[]
    for n in (12,18,24):
        cases.append((f'chain-{n}',n,[[i,i+1] for i in range(1,n)]))
        cases.append((f'disconnected-{n}',n,[[i,i+1] for i in range(1,n,2)]))
    for i in range(6):
        n=12;clauses=[[r.choice((-1,1))*v for v in r.sample(range(1,n+1),3)] for _ in range(30)]
        cases.append((f'dense-{i}',n,clauses))
    rows=[]
    for name,n,clauses in cases:
        timing={};raw={};result=None
        for label,fn in [('reference_cached_dpll',lambda:reference_count(n,clauses)),('separator_tables',lambda:count_cnf(n,clauses))]:
            times=[]
            for _ in range(5):
                start=time.perf_counter();result=fn();times.append(time.perf_counter()-start)
            timing[label]=statistics.median(times);raw[label]=times
            if label=='reference_cached_dpll':expected=result
        assert result['count']==expected
        rows.append({'case':name,'variables':n,'clauses':len(clauses),'count':expected,'median_seconds':timing,'raw_seconds':raw,
                     'width_upper_bound':result['decomposition']['width'],'cells_visited':result['cells_visited'],
                     'cache_hits':result['message_cache_hits']})
    large=count_cnf(200,[[i,i+1] for i in range(1,201,2)])
    assert large['count']==3**100
    receipt={'schema':'pp-graph-benchmark/1','seed':20261011,'repetitions':5,'python':platform.python_version(),
             'platform':platform.platform(),'rows':rows,'large_exact_case':large,
             'scope':'12 synthetic instances; internal cached DPLL baseline; no external-solver or industrial speedup claim',
             'summed_median_seconds':{k:sum(row['median_seconds'][k] for row in rows) for k in timing}}
    Path('receipts/graph_methods/benchmark.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt['summed_median_seconds'],indent=2))


if __name__=='__main__':main()
