"""Repeatable public budgeting workflow and independent recursive comparison."""
import argparse
import gc
import hashlib
import json
from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
from statistics import median
from time import perf_counter
from perfectpower.participatory_budgeting import BudgetElection,BudgetSession
from perfectpower.planning import CompletionPlanner
from perfectpower.planning_native import library,recursive_reference
from run_planning import ortools_optimum
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/budget_lab'

class RecursiveIndex:
    def __init__(self,planner):
        self.p=planner;self.lib=library();self.scale=1;self.cache={}
    def query(self,prefix):
        self.p._mask(prefix);key=tuple(prefix)
        if key in self.cache:return self.cache[key]
        spec=deepcopy(self.p.specification);used=[sum(x*v['costs'][k] for x,v in zip(prefix,spec['variables'])) for k in range(len(spec['resources']))]
        score=sum(Q(v['profit'])*x for x,v in zip(prefix,spec['variables']));mask=0
        for x in prefix:mask=2*mask+x
        mask <<=len(spec['variables'])-len(prefix)
        if any(u>r['max'] for u,r in zip(used,spec['resources'])):r={'count':0,'best':0,'ties':0,'mask':0,'records':0}
        elif len(prefix)==len(spec['variables']):r={'count':1,'best':int(score),'ties':1,'mask':mask,'records':0}
        else:
            for resource,u in zip(spec['resources'],used):resource['max']-=u
            spec['variables']=spec['variables'][len(prefix):]
            reference,scale=recursive_reference(CompletionPlanner(spec,_compile=False))
            assert scale==1 and score.denominator==1,'public support integral'
            r=dict(reference,best=reference['best']+int(score),mask=reference['mask']|mask)
        self.cache[key]=r;return r

def reference_planner(spec):
    p=CompletionPlanner(dict(spec,strategy='mitm'),_compile=False);p.index=RecursiveIndex(p);p.root_entry=p._indexed_entry(())
    return p

def workflow(session):
    # New prefixes / ranks in every bank; rank-return validation uses a second fresh session below.
    e=session.election;n=len(e.projects);out=[]
    for percent in (100,90,80):
        budget=e.budget*percent//100
        locks={e.projects[0]['project_id']:1,e.projects[-1]['project_id']:0} if percent==90 else {}
        base={'budget':budget,'locks':locks};view=session.evaluate(base);out.append(view)
        count=view['count']
        if not count:continue
        for rank in sorted({0,count//7,count//3,2*count//3,count-1}):
            chosen=session.evaluate(dict(base,operation='select',rank=rank));out.append(chosen)
            inverse=session.evaluate(dict(base,operation='rank',point=chosen['plan']['point']));assert inverse['rank']==rank;out.append(inverse)
        for seed in (37,104,999):out.append(session.evaluate(dict(base,operation='sample',seed=seed)))
    return out

def benchmark(repeats):
    manifest=json.loads((ROOT/'data/participatory_budgeting/manifest.json').read_text());t=perf_counter();lib=library();compilation=perf_counter()-t
    ledger={'schema':'pp-budget-lab-benchmark/1','source_snapshot':manifest['commit'],'native':lib._provenance,'native_compile_seconds':compilation,'repeats':repeats,
            'scope':'Three complete scenarios (100%,90%,80% total budget), one nonprefix include/exclude commitment, five select/rank pairs and three seeded uniform samples per nonempty scenario; parsing timed separately; cold includes construction; warm retains three scenarios',
            'baseline':'Independent original-variable recursive subcube counting using native integers; shares presentation and rank decomposition but computes completion counts/maxima by a different algorithm', 'cases':[]}
    OUT.mkdir(parents=True,exist_ok=True)
    for row in manifest['files']:
        raw=(ROOT/'data/participatory_budgeting/raw'/row['filename']).read_bytes();assert hashlib.sha256(raw).hexdigest()==row['sha256']
        t=perf_counter();e=BudgetElection(raw.decode('utf8'),row);parsing=perf_counter()-t
        record={'id':row['id'],'election':e.summary(),'parsing_seconds':parsing,'measurements':{'planner_cold':[],'planner_warm':[],'reference_cold':[],'reference_warm':[]},'optimization_only':{'planner':[],'ortools':[]}}
        expected=None
        for trial in range(repeats):
            variants=[('planner',CompletionPlanner),('reference',reference_planner)]
            if trial%2:variants.reverse()
            for name,constructor in variants:
                gc.collect();t=perf_counter();session=BudgetSession(e,constructor);answer=workflow(session);record['measurements'][name+'_cold'].append(perf_counter()-t)
                if expected is None:expected=answer
                assert answer==expected,'complete budgeting answers differ'
                # Replay inverse ranks on fresh caches: selected-result caches cannot establish correctness.
                verifier=BudgetSession(e,constructor)
                for response in answer:
                    if response.get('plan') is not None and response.get('count'):
                        point=response['plan']['point'];rank=session.evaluate({'budget':response['budget'],'locks':response['locks'],'operation':'rank','point':point})['rank']
                        assert verifier.evaluate({'budget':response['budget'],'locks':response['locks'],'operation':'rank','point':point})['rank']==rank
                t=perf_counter()
                for _ in range(5):assert workflow(session)==expected
                record['measurements'][name+'_warm'].append((perf_counter()-t)/5)
                del session,verifier;gc.collect()
        from perfectpower.planning import optimize_allocation
        for trial in range(repeats):
            variants=[('planner',optimize_allocation),('ortools',ortools_optimum)]
            if trial%2:variants.reverse()
            for name,solver in variants:
                t=perf_counter();r=solver(e.specification);record['optimization_only'][name].append(perf_counter()-t)
                assert r['optimal'] and Q(r['maximum'])==Q(expected[0]['maximum'])
        record['median_seconds']={k:median(v) for k,v in record['measurements'].items()};record['optimization_median_seconds']={k:median(v) for k,v in record['optimization_only'].items()}
        record['answers']=expected;record['requests_per_workflow']=len(expected)
        # Deterministic application receipt and source-bound model.
        model={'schema':'pp-budget-election/1','source':row,'summary':e.summary(),'specification':e.specification}
        (OUT/(row['id']+'.json')).write_text(json.dumps(model,indent=2,ensure_ascii=False)+'\n')
        ledger['cases'].append(record);(OUT/'benchmark.json').write_text(json.dumps(ledger,indent=2,ensure_ascii=False)+'\n')
        print(json.dumps({'case':row['id'],'count':expected[0]['count'],'maximum':expected[0]['maximum'],'seconds':record['median_seconds']}),flush=True)
    return ledger

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repeats',type=int,default=3);a=p.parse_args()
    if not 1<=a.repeats<=10:p.error('repeats must be 1..10')
    benchmark(a.repeats)
