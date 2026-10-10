"""Reproduce planner examples, public workload coverage and scoped comparisons."""
import argparse
import gc
import hashlib
import json
import platform
from collections import Counter
from fractions import Fraction as Q
from math import lcm, comb
from pathlib import Path
from statistics import median
from time import perf_counter
from random import Random
from perfectpower.planning import CompletionPlanner
from perfectpower.planning_cli import execute
from perfectpower.divisor_square import WorkLimit

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'receipts/planning'


def parse_public():
    data = (ROOT/'data/planning/mknap1.txt').read_text()
    tokens = iter(data.split()); result = []
    for _ in range(int(next(tokens))):
        n,m = int(next(tokens)),int(next(tokens)); optimum = next(tokens)
        profits = [next(tokens) for j in range(n)]
        matrix = [[int(next(tokens)) for j in range(n)] for i in range(m)]
        capacity = [int(next(tokens)) for i in range(m)]
        spec = {'kind':'allocation','resources':[{'name':f'resource_{i+1}','max':capacity[i]} for i in range(m)],
                'variables':[{'name':f'project_{j+1}','costs':[matrix[i][j] for i in range(m)],'profit':profits[j],'upper':1} for j in range(n)]}
        result.append({'name':f'petersen_{n}','published_optimum':optimum,'specification':spec})
    assert list(tokens)==[]
    assert result == json.loads((ROOT/'data/planning/petersen.json').read_text()), 'public transcription differs'
    return result


def illustrative_specs():
    model={'observations':[0]*4,'actions':{'skip':[0,1,2,3],'take':[1,0,3,2]}}
    slots={'kind':'allocation','strategy':'dp','resources':[{'name':'capacity','max':30}],
           'variables':[{'name':f'slot_{i+1}','costs':[1],'upper':1,'actions':{'0':'skip','1':'take'}} for i in range(60)],
           'machine':{'model':model,'initial':0,'accepting':[0,2]}}
    huge={'kind':'allocation','resources':[{'name':'budget','min':10**12,'max':10**12}],
          'variables':[{'name':f'resource_{i}','costs':[w],'upper':None,'profit':w} for i,w in enumerate((1,2,1,2))]}
    words={'kind':'words','budget':24,'machine':{'model':model,'initial':0,'accepting':[0,2]},
           'actions':[{'name':'skip','cost':2,'profit':'1/3'},{'name':'take','cost':1,'profit':1}]}
    return {'compatible_slots':slots, 'huge_allocation':huge, 'ordered_actions':words}


def bank(planner):
    total=planner.count(); ranks=sorted({0,total//4,total//2,3*total//4,total-1})
    result=[]
    for rank in ranks:
        point=planner.select(rank)
        result.append({'rank':rank,'point':point,'reverse_rank':planner.rank(point),
                       'prefix_count':planner.completions(point[:3])['count']})
    return {'count':total,'optimization':planner.optimize(),'bank':result}


class GrayIndex:
    """Independent exhaustive binary baseline with sorted masks and prefix index."""
    def __init__(self,spec):
        variables=spec['variables']; n=len(variables); m=len(spec['resources'])
        assert not spec.get('machine') and all(v['upper']==1 and v.get('lower',0)==0 for v in variables)
        self.n=n; caps=[r['max'] for r in spec['resources']]
        profit=[Q(v['profit']) for v in variables]; scale=lcm(*(p.denominator for p in profit))
        profit=[int(p*scale) for p in profit]
        used=[0]*m; value=0; previous=0; feasible=[]; best=None; optimizers=[]
        for i in range(1<<n):
            mask=i^(i>>1)
            if i:
                changed=mask^previous; j=n-changed.bit_length(); sign=1 if mask&changed else -1
                weights=variables[j]['costs']
                for k in range(m):used[k]+=sign*weights[k]
                value+=sign*profit[j]
            if all(u<=c for u,c in zip(used,caps)):
                feasible.append(mask)
                if best is None or value>best:best=value;optimizers=[mask]
                elif value==best:optimizers.append(mask)
            previous=mask
        self.masks=sorted(feasible); self.indices={mask:i for i,mask in enumerate(self.masks)}
        self.prefixes=Counter(mask >> max(0,n-3) for mask in self.masks)
        self.optimum={'maximum':str(Q(best,scale)), 'maximizer_count':len(optimizers),'point':self.decode(min(optimizers))}
    def decode(self,mask):return [(mask>>(self.n-1-i))&1 for i in range(self.n)]
    def count(self):return len(self.masks)
    def select(self,rank):return self.decode(self.masks[rank])
    def rank(self,point):return self.indices[int(''.join(map(str,point)),2)]
    def completions(self,prefix):
        assert len(prefix)==min(3,self.n)
        return {'count':self.prefixes[int(''.join(map(str,prefix)),2)]}
    def optimize(self):return self.optimum


def ortools_optimum(spec):
    from ortools.algorithms.python import knapsack_solver as K
    variables=spec['variables']; values=[Q(v['profit']) for v in variables]
    scale=lcm(*(v.denominator for v in values)); integers=[int(v*scale) for v in values]
    weights=[[v['costs'][i] for v in variables] for i in range(len(spec['resources']))]
    solver=K.KnapsackSolver(K.SolverType.KNAPSACK_MULTIDIMENSION_BRANCH_AND_BOUND_SOLVER,'PublicProjects')
    solver.set_time_limit(10)
    solver.init(integers,weights,[r['max'] for r in spec['resources']]); value=solver.solve()
    point=[int(solver.best_solution_contains(i)) for i in range(len(variables))]
    if any(sum(x*w for x,w in zip(point,row))>resource['max'] for row,resource in zip(weights,spec['resources'])) or sum(x*v for x,v in zip(point,integers))!=value:
        raise AssertionError('baseline witness does not satisfy original exact constraints')
    return {'maximum':str(Q(value,scale)),'point':point,'optimal':solver.is_solution_optimal()}


def benchmark(rows,repeats):
    import ortools
    public=[]
    for row in rows:
        spec=dict(row['specification'])
        if len(spec['variables'])==20:spec['state_limit']=1000000
        measurements={'planner_cold':[],'planner_bank_warm':[],'gray_cold':[],'gray_bank_warm':[],'ortools_optimization_only':[]}
        record={'name':row['name'],'variables':len(spec['variables']),'constraints':len(spec['resources']),
                'published_optimum':row['published_optimum'],'state_limit':spec.get('state_limit',200000)}
        # Large public cases retain an explicit unresolved counting outcome.
        if len(spec['variables'])>20:
            t=perf_counter()
            try:
                planner=CompletionPlanner(spec);record['planner']={'status':'complete','summary':planner.summary()}
            except WorkLimit as error:
                record['planner']={'status':'WORK_LIMIT','reason':str(error)}
            record['planner_attempt_seconds']=perf_counter()-t
        else:
            expected=None
            for trial in range(repeats):
                variants=[('planner',CompletionPlanner),('gray',GrayIndex)]
                if trial%2:variants.reverse()
                for name,constructor in variants:
                    gc.collect();start=perf_counter();obj=constructor(spec);answer=bank(obj)
                    measurements[name+'_cold'].append(perf_counter()-start)
                    if expected is None:expected=answer
                    if answer!=expected:raise AssertionError('public complete-query answers differ')
                    start=perf_counter()
                    for _ in range(20):bank(obj)
                    measurements[name+'_bank_warm'].append((perf_counter()-start)/20)
                    if name=='planner':record['planner']={'status':'complete','summary':obj.summary()}
                    del obj;gc.collect()
            record['exact_answers']=expected
        for _ in range(repeats):
            start=perf_counter();baseline=ortools_optimum(spec)
            measurements['ortools_optimization_only'].append(perf_counter()-start)
            if not baseline['optimal'] or Q(baseline['maximum'])!=Q(row['published_optimum']):
                raise AssertionError('public objective baseline differs from published optimum')
        record['ortools']=baseline; record['seconds']=measurements
        record['median_seconds']={k:median(v) for k,v in measurements.items() if v}
        public.append(record)
        print(json.dumps({'case':row['name'],'status':record['planner']['status']}),flush=True)
    return {'schema':'pp-planning-benchmark/1','public_cases':public,'repeats':repeats,'python':platform.python_version(),
            'ortools_version':ortools.__version__, 'cold_scope':'model construction and five select/rank/prefix queries plus count and optimum',
            'warm_scope':'same five-query bank on a retained compiled model, mean of 20 repetitions per trial',
            'baseline_scope':'Gray enumeration answers the full query bank; OR-Tools solves optimization only and is not a counting comparison',
            'limitations':'public historical R&D benchmarks, not a customer deployment; larger exact counts explicitly unresolved; no universal or industrial solver speedup claim'}


def write(path,value):path.write_text(json.dumps(value,indent=2,default=str)+'\n')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--benchmark',action='store_true');parser.add_argument('--repeats',type=int,default=3)
    parser.add_argument('--kernel-check',action='store_true');args=parser.parse_args()
    if not 1<=args.repeats<=10:parser.error('repeats must be 1..10')
    OUT.mkdir(parents=True,exist_ok=True); rows=parse_public()
    results={}
    for name,spec in illustrative_specs().items():
        request={'specification':spec,'seed':37,'queries':[{'method':'summary'},{'method':'sample'},
                  {'method':'select','args':{'rank':0,'optimal':True}},{'method':'evidence'}]}
        path=ROOT/f'examples/planning/{name}.json';write(path,request)
        result=execute(request);write(OUT/f'{name}.json',result);results[name]=result['summary']
    slots=CompletionPlanner(illustrative_specs()['compatible_slots'])
    assert slots.count()==sum(comb(60,k) for k in range(0,31,2))
    changed=slots.with_resources([{'name':'capacity','max':28}])
    assert changed.count()==sum(comb(60,k) for k in range(0,29,2))
    write(OUT/'resource_change.json',{'original':slots.summary(),'changed':changed.summary()})
    write(OUT/'petersen_6.json',execute(json.loads((ROOT/'examples/planning/petersen_6.json').read_text())))
    from perfectpower.checked_soe import compile_soe,accept_soe
    proof=compile_soe(slots.machine_model,slots.quotient)
    (OUT/'Compatibility.lean').write_text(proof['lean'])
    if args.kernel_check:
        accepted=accept_soe(slots.machine_model,slots.quotient)
        write(OUT/'soe_kernel.json',accepted)
        if not accepted['accepted']:raise ValueError(accepted['reason'])
    results['compatibility_proposal']={'source_sha256':proof['source_sha256'],'kernel_checked':args.kernel_check,
                                     'scope':proof['scope']}
    write(OUT/'summary.json',results)
    if args.benchmark:write(OUT/'benchmark.json',benchmark(rows,args.repeats))
    print(json.dumps(results,indent=2))


if __name__=='__main__':main()
