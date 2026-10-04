"""Apply redesigned mechanisms to the full stored arithmetic corpus, stdlib only.

Deterministic receipts are separate from optional current-host timing data.
The historical papers/projects inspire the mechanisms; their original
experiments are not reproduced or needed for these new algorithms.
"""
import argparse
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
from time import perf_counter
from perfectpower import polyalg as P
from perfectpower import exact_linear as E
from perfectpower.arithmetic_engine import ArithmeticEngine,verify_result
from perfectpower.closest_integer import IntegerLiftOptimizer,verify_optimum
from perfectpower.deep_recovery_cli import exact_json
from perfectpower.polynomial_symmetry import pullback_points
from recover_deep_gems import audit_quartic_inputs

ROOT=Path(__file__).resolve().parents[1]


def expanded(outer,power,a=1,b=0):
    f=[0]*(power*(len(outer)-1)+1)
    for i,c in enumerate(outer):f[i*power]=c
    return tuple(f) if (a,b)==(1,0) else tuple(map(int,P.compose_linear(P.poly(f),b,a)))


def build(output,benchmark=False):
    out=Path(output);out.mkdir(parents=True,exist_ok=True);hashes={}
    def read(path):
        text=(ROOT/path).read_text();hashes[path]=hashlib.sha256(text.encode()).hexdigest();return text
    def write(name,data):
        (out/name).write_text(json.dumps(data,sort_keys=True,indent=2,default=exact_json)+'\n')
    corpus=json.loads(read('receipts/divisor_sum/complete_quartics.json'))
    audit=audit_quartic_inputs(corpus,read('receipts/divisor_sum/CompleteQuartics.lean'),json.loads(read('receipts/divisor_sum/lean_catalogue_validation.json')))
    previous=json.loads(read('receipts/deep_gems/quartic_pullbacks.json'))['rows']
    engine=ArithmeticEngine();rows=[];counts={'plain':0,'affine':0};root_checks=0;raw_width=0;checked=0
    start=perf_counter();n=10**30
    for index,row in enumerate(corpus['rows']):
        for q in (2,3):
            reference=previous[2*index+(q-2)]
            expected=sorted(tuple(p) for p in reference['points'])
            assert expected==pullback_points(row['coefficients'],row['points'],q)['points']
            for mode in ('plain','affine'):
                a,b=(1,0) if mode=='plain' else (2+index%4,-(2+index%4)*n-index%(2+index%4))
                f=expanded(row['coefficients'],q,a,b)
                result=engine.solve(f,strict=True)
                wanted=expected if mode=='plain' else sorted(((x-b)//a,y) for x,y in expected if (x-b)%a==0)
                assert result['points']==wanted,(index,q,mode)
                assert verify_result(result),(index,q,mode,'certificate')
                stats=result['statistics'];counts[mode]+=len(wanted);root_checks+=stats['candidates_checked'];raw_width+=stats.get('interval_size',0);checked+=1
                rows.append({'source_row':index,'power':q,'variant':mode,'affine':[a,b],
                    'points':wanted,'leaf_degree':stats.get('leaf_degree'),'leaf_interval_size':stats.get('interval_size',0),
                    'root_checks':stats['candidates_checked'],'certificate_replayed':True})
        if index and index%500==0:print(f'Completed {index+1}/{len(corpus["rows"])} source rows',flush=True)
    seconds=perf_counter()-start
    write('corpus.json',{'outer_audit':audit,'source_rows':len(corpus['rows']),'queries':checked,'point_counts':counts,
        'surviving_root_checks':root_checks,'summed_leaf_interval_widths':raw_width,
        'cache_hits':engine.hits,'cache_misses':engine.misses,'rows':rows,
        'scope':'all stored square/cube pullbacks and constructed affine disguises; all-integer complete equations, independent Python certificate replay, no new Lean compilation'})
    hard=[]
    for outer,q,a,b,d in (([1,1,0,0,1],3,2,-2*n-1,2),([1,-1,0,0,1],10,7,-7*n-1,2),([1,1,0,1],5,2,-2*n-1,3)):
        packet=engine.solve(expanded(outer,q,a,b),d,strict=True);assert verify_result(packet);hard.append(packet)
    obstruction=engine.solve([3,0,0,0,2],2);assert verify_result(obstruction) and obstruction['points']==[]
    write('hard_examples.json',{'giant_coordinate_examples':hard,'global_local_obstruction':obstruction})
    arithmetic=json.loads(read('receipts/divisor_kernel/results.json'))['corpus']
    counts_by_degree=[arithmetic['hit_counts'][str(d)] for d in arithmetic['degrees']]
    optimizer=IntegerLiftOptimizer([counts_by_degree],arithmetic['sigma_gcd_gram'])
    target=[Q(6,5),Q(-1,7),Q(1,9),Q(-1,11),Q(1,13),Q(1,17),Q(-1,19)]
    decoded=optimizer.nearest([counts_by_degree[0]],target);assert verify_optimum(decoded)
    assert decoded['minimizers']==[(1,0,0,0,0,0,0)]
    write('corpus_integer_metric.json',{'degrees':arithmetic['degrees'],'observation':counts_by_degree,'result':decoded,
        'scope':'closest integer combination of seven actual divisor-feature vectors with a fixed aggregate observation; no prediction of unseen powers'})
    generic=IntegerLiftOptimizer([[2,3]]);batch=[]
    for b in range(-20,21):
        packet=generic.nearest([b],[n,n+Q(1,3)]);assert verify_optimum(packet)
        batch.append({k:packet[k] for k in ('rhs','target','minimizers','minimum_energy','continuous_minimum','enumeration_nodes')})
    tied=IntegerLiftOptimizer([[1,1]]).nearest([1],[0,0]);assert verify_optimum(tied)
    write('integer_batches.json',{'shared_smith_metric_decompositions':1,'right_hand_sides':len(batch),'rows':batch,'tied_example':tied})
    cells=json.loads(read('receipts/branched_geometry/cell_models.json'));cell_results=[]
    for cell in cells:
        if cell['genus']>4:continue
        a=E.transpose(cell['boundary2']);edges=cell['edges'];mass=[[i+3 if i==j else 0 for j in range(edges)] for i in range(edges)]
        solver=IntegerLiftOptimizer(a,mass);packet=solver.nearest([0]*len(a),[Q((i%3)-1,3) for i in range(edges)])
        assert verify_optimum(packet)
        cell_results.append({'genus':cell['genus'],'edges':edges,'result':packet,'scope':'integer weighted coclosed edge vectors of the stored canonical cell model'})
    write('integer_cells.json',{'models':cell_results,'genus7_status':'14-dimensional kernel exceeds the default 12-parameter budget; not optimized here'})
    summary={'source_sha256':hashes,'queries':checked,'point_counts':counts,'all_certificates_replayed':True,
        'surviving_root_checks':root_checks,'summed_leaf_interval_widths':raw_width,
        'cache_hits':engine.hits,'cache_misses':engine.misses,'giant_example_degrees':[12,40,15],
        'giant_example_root_checks':[p['statistics']['candidates_checked'] for p in hard],
        'actual_metric_basis_operations':len(optimizer.operations),'actual_metric_enumeration_nodes':decoded['enumeration_nodes'],
        'integer_batch_queries':len(batch),'integer_cell_genera':[p['genus'] for p in cell_results],
        'new_lean_compilations':0,'execution_verified':False}
    write('summary.json',summary)
    if benchmark:write('benchmark.json',{'corpus_seconds':seconds,'scope':'single current-host end-to-end corpus solving AND certificate replay; not a comparison against an industrial solver'})
    return summary


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=ROOT/'receipts/enhanced_machinery');p.add_argument('--benchmark',action='store_true')
    print(json.dumps(build(p.parse_args().output,p.parse_args().benchmark),sort_keys=True,indent=2))
