"""Develop mixed-locality filters and observable machines on stored workloads."""
import argparse
import hashlib
import json
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
from statistics import median
from time import perf_counter
from enhance_machinery import build as build_arithmetic
from perfectpower.deep_recovery_cli import exact_json
from perfectpower.residue_cover import residue_cover,scan_cover
from perfectpower.factored_sieve import power_residue,factored_cover,scan_factored,verify_factored_cover
from perfectpower.observable_machine import recurrence_batch,minimal_machine,verify_machine,word_output,power_outputs
from perfectpower.recurrence import Recurrence
from perfectpower.arithmetic_engine import ArithmeticEngine,verify_result

ROOT=Path(__file__).resolve().parents[1]


def build(output,*,benchmark=False):
    out=Path(output);out.mkdir(parents=True,exist_ok=True);hashes={}
    def read(path):
        data=(ROOT/path).read_bytes();hashes[path]=hashlib.sha256(data).hexdigest();return json.loads(data)
    def write(name,value):
        (out/name).write_text(json.dumps(value,sort_keys=True,indent=2,default=exact_json)+'\n')
    arithmetic=build_arithmetic(out/'arithmetic')
    previous=read('receipts/monograph_development/arithmetic/summary.json')
    assert arithmetic['queries']==previous['queries'] and arithmetic['point_counts']==previous['point_counts']
    assert arithmetic['surviving_root_checks']<=previous['surviving_root_checks']
    models=read('receipts/sequence_recovery/results.json')['oeis_scan']['candidates'];groups=defaultdict(list)
    for row in models:groups[tuple(row['coefficients'])].append(row)
    machines=[];unshared=shared=checks=0
    for coefficients,rows in sorted(groups.items()):
        definitions=[Recurrence(tuple(map(Q,row['coefficients'])),tuple(map(Q,row['initial']))) for row in rows]
        machine=recurrence_batch(definitions);assert verify_machine(machine)
        for n in (0,1,2,10,50,100):
            assert power_outputs(machine,n)==tuple(m.nth(n) for m in definitions);checks+=len(rows)
        unshared+=machine['state_dimension'];shared+=machine['minimal_dimension']
        machines.append({'ids':[r['id'] for r in rows],'definition_status':'supplied reconstructed recurrence models; not OEIS definition proofs',
            'machine':machine,'checked_indices':[0,1,2,10,50,100]})
    write('recurrence_machines.json',{'source_models':len(models),'groups':len(machines),'unshared_state_coordinates':unshared,
        'minimal_shared_coordinates':shared,'independent_nth_comparisons':checks,'machines':machines})
    directional=minimal_machine([[[1,1],[0,1]],[[1,0],[1,1]]],[1,0],[[1,0]])
    execution=word_output(directional,[0,1]);written=word_output(directional,[0,1],order='written')
    assert execution==(1,) and written==(2,)
    zero=minimal_machine([[[2,1],[0,3]]],[1,2],[[0,0]])
    hidden=minimal_machine([[[2,0,0],[0,3,0],[0,0,7]]],[1,1,0],[[1,0,0]])
    write('observable_examples.json',{'noncommuting':directional,'execution_output':execution,'written_output':written,
        'zero_future_output':zero,'unreachable_and_unobservable':hidden})
    depth_checks=0
    for p in (2,3,5,7):
        for a in (1,2,3,4):
            q=p**a
            for d in range(2,17):
                image={pow(x,d,q) for x in range(q)}
                for x in range(q):assert power_residue(x,d,p,a)==(x in image);depth_checks+=1
    examples=[];timings=[]
    problems=[('quadratic-square offset',[-10**10,1,0,0,1],2,-100000,100000),
        ('degree-64 tenth powers',[1,1]+[0]*62+[1],10,-10000,10000),
        ('cubic powers with a far exceptional root',[-10**20,1,0,0,0,0,1],3,-100000,100000)]
    for name,f,d,lo,hi in problems:
        base=residue_cover(f,d);cover=factored_cover(base);assert verify_factored_cover(cover)
        old=scan_cover(base,lo,hi);new=scan_factored(cover,lo,hi);assert old['points']==new['points']
        examples.append({'name':name,'cover':cover,'old':old,'new':new,'scope':'complete only within the supplied scan interval'})
        if benchmark:
            old_times=[];new_times=[]
            for repeat in range(5):
                order=((scan_cover,base,old_times),(scan_factored,cover,new_times)) if repeat%2==0 else ((scan_factored,cover,new_times),(scan_cover,base,old_times))
                for fn,c,times in order:
                    start=perf_counter();result=fn(c,lo,hi);times.append(perf_counter()-start);assert result['points']==old['points']
            timings.append({'name':name,'repeats':5,'legacy_seconds':old_times,'factored_seconds':new_times,
                'legacy_median_seconds':median(old_times),'factored_median_seconds':median(new_times),
                'scope':'alternating current-host warm-cache bounded scan, includes receipt replay; excludes initial cover construction'})
    complete=ArithmeticEngine().solve([-10**20,1,0,0,0,0,1],3,strict=True);assert verify_result(complete)
    assert complete['points']==[(10**20,10**40)]
    write('locality_examples.json',{'independent_exhaustive_residue_comparisons':depth_checks,'bounded_examples':examples,
        'complete_cubic_power_result':complete,'exceptional_point_outside_central_scan':[10**20,10**40]})
    summary={'schema':'pp-lost-work-development/1','execution_verified':False,'new_lean_compilations':0,
        'arithmetic_queries':arithmetic['queries'],'point_counts':arithmetic['point_counts'],
        'previous_root_checks':previous['surviving_root_checks'],'current_root_checks':arithmetic['surviving_root_checks'],
        'recurrence_models':len(models),'recurrence_groups':len(machines),'unshared_state_coordinates':unshared,
        'minimal_shared_coordinates':shared,'independent_recurrence_value_checks':checks,
        'independent_exhaustive_residue_comparisons':depth_checks,'large_combined_modulus':examples[0]['cover']['modulus'],
        'tenth_power_root_checks_before':examples[1]['old']['candidates_checked'],
        'tenth_power_root_checks_after':examples[1]['new']['candidates_checked'],
        'complete_exceptional_point':[10**20,10**40],'source_sha256':hashes,
        'scope':'complete supported integer equations and all finite words of supplied rational models; no general integer solver or primitive-call optimality claim'}
    write('summary.json',summary)
    if benchmark:write('benchmark.json',{'rows':timings,'new_lean_compilations':0})
    print(json.dumps(summary,indent=2),flush=True);return summary


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=ROOT/'receipts/lost_work_development')
    parser.add_argument('--benchmark',action='store_true');args=parser.parse_args();build(args.output,benchmark=args.benchmark)
