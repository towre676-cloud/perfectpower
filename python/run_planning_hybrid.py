"""Independent exact comparisons for the hybrid planner; compiler time explicit."""
import argparse
import gc
import hashlib
import json
import platform
try:
    import resource
except ImportError:
    resource=None
from fractions import Fraction as Q
from pathlib import Path
from statistics import median
from time import perf_counter
from perfectpower.planning import CompletionPlanner,Entry,optimize_allocation
from perfectpower.planning_native import NativeIndex,library,recursive_reference
from perfectpower.divisor_square import WorkLimit
from run_planning import parse_public,bank,GrayIndex,ortools_optimum

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/planning/hybrid'

def native_exhaustive(spec):
    p=CompletionPlanner(dict(spec,strategy='mitm'),_compile=False)
    p.index=NativeIndex(p,exhaustive=True);p.root_entry=p._indexed_entry(())
    return p

def benchmark(repeats=3,large=False):
    start=perf_counter();lib=library();compilation=perf_counter()-start
    result={'schema':'pp-planning-hybrid-benchmark/1','python':platform.python_version(), 'repeats':repeats,
            'native':lib._provenance,'native_compile_and_load_seconds':compilation,
            'timing_scope':'compiler initialized once; each cold workflow constructs a fresh index and runs the same five-query bank; warm bank mean of 20 repetitions',
            'memory_scope':'Linux cumulative process peak RSS after each case, includes interpreter, optional solver and native compiler child excluded; not per-variant isolated peak',
            'cases':[]}
    for row in parse_public():
        spec=row['specification'];n=len(spec['variables']);record={'name':row['name'],'published_optimum':row['published_optimum']}
        trials={'mitm_cold':[],'mitm_warm':[],'native_exhaustive_cold':[],'native_exhaustive_warm':[], 'python_gray_cold':[], 'python_gray_warm':[]}
        expected=None
        if n<=20:
            variants=[('mitm',lambda s:CompletionPlanner(dict(s,strategy='mitm'))),('native_exhaustive',native_exhaustive),('python_gray',GrayIndex)]
            for repeat in range(repeats):
                for name,constructor in variants[repeat%3:]+variants[:repeat%3]:
                    gc.collect();t=perf_counter();p=constructor(spec);answer=bank(p);trials[name+'_cold'].append(perf_counter()-t)
                    if expected is None:expected=answer
                    assert answer==expected,'independent complete workflows differ'
                    t=perf_counter()
                    for _ in range(20):assert bank(p)==expected
                    trials[name+'_warm'].append((perf_counter()-t)/20)
                    del p
            record['counting']={'status':'complete','answers':expected}
        elif n==28 or large and n==39:
            t=perf_counter()
            try:
                p=CompletionPlanner(dict(spec,strategy='mitm'));compile_seconds=perf_counter()-t
                answer=bank(p);elapsed=perf_counter()-t
                record['counting']={'status':'complete','answers':answer,'cold_seconds':elapsed,'index_seconds':compile_seconds,'query_node_visits':p.index.query_visits,'right_records':p.index.query(())['records']}
                if n==28:
                    t=perf_counter();reference,scale=recursive_reference(CompletionPlanner(spec,_compile=False))
                    assert reference['count']==answer['count'] and Q(reference['best'],scale)==Q(answer['optimization']['maximum']) and reference['ties']==answer['optimization']['maximizer_count']
                    point=p._decode(reference['mask']);assert point==answer['optimization']['point']
                    record['independent_recursive_reference']={'answer':reference,'seconds':perf_counter()-t}
                if n==39:
                    checks=[]
                    for chosen in answer['bank']:
                        prefix=chosen['point'][:20];used=[sum(x*v['costs'][k] for x,v in zip(prefix,spec['variables'])) for k in range(len(spec['resources']))]
                        suffix={'kind':'allocation','resources':[dict(r,min=max(0,r.get('min',0)-u),max=r['max']-u) for r,u in zip(spec['resources'],used)],'variables':spec['variables'][20:]}
                        reference,scale=recursive_reference(CompletionPlanner(suffix,_compile=False))
                        actual=p.completions(prefix);assert reference['count']==actual['count']
                        prefix_score=sum(Q(v['profit'])*x for x,v in zip(prefix,spec['variables']))
                        assert Q(reference['best'],scale)+prefix_score==Q(actual['maximum']) and reference['ties']==actual['maximizer_count']
                        checks.append({'prefix':prefix,'count':actual['count'],'maximum':actual['maximum'],'reference_nodes':reference['visits']})
                    record['independent_prefix_checks']=checks
                del p
            except WorkLimit as e:record['counting']={'status':'WORK_LIMIT','reason':str(e),'seconds':perf_counter()-t}
        else:record['counting']={'status':'not_run','reason':'39-case requires --large; 50-case exceeds bounded MITM record support; full count remains unresolved'}
        record['seconds']=trials;record['median_seconds']={k:median(v) for k,v in trials.items() if v}
        opt={'native':[],'ortools':[]}
        for repeat in range(repeats):
            for name,solver in ([('native',optimize_allocation),('ortools',ortools_optimum)] if repeat%2==0 else [('ortools',ortools_optimum),('native',optimize_allocation)]):
                t=perf_counter();r=solver(spec);opt[name].append(perf_counter()-t)
                assert r['optimal'] and Q(r['maximum'])==Q(row['published_optimum'])
                record[name+'_optimization']=r
        record['optimization_seconds']=opt;record['optimization_median_seconds']={k:median(v) for k,v in opt.items()}
        record['process_peak_rss_bytes']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024 if resource is not None and platform.system()=='Linux' else None
        result['cases'].append(record)
        print(json.dumps({'case':row['name'],'count_status':record['counting']['status'],'opt_seconds':record['optimization_median_seconds']}),flush=True)
        OUT.mkdir(parents=True,exist_ok=True);(OUT/'benchmark.json').write_text(json.dumps(result,indent=2)+'\n')
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repeats',type=int,default=3);p.add_argument('--large',action='store_true');a=p.parse_args()
    if not 1<=a.repeats<=10:p.error('repeats must be 1..10')
    benchmark(a.repeats,a.large)
