"""Rebuild witness resolvents and graph repairs from retained exact workloads."""
import argparse
import hashlib
import json
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path
from perfectpower.deep_recovery_cli import exact_json
from perfectpower.recurrence import Recurrence
from perfectpower.recurrence_identity import companion
from perfectpower.witness_resolvent import (witness_resolvent,verify_resolvent,
    resolvent_value,reduced_fraction,subsequence_resolvent)
from perfectpower.connection_measure import ConnectionMeasure,verify_measure
from perfectpower.connection_updates import reweight,verify_reweight

ROOT=Path(__file__).resolve().parents[1]


def build(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True);hashes={}
    def read(path):
        raw=(ROOT/path).read_bytes();hashes[path]=hashlib.sha256(raw).hexdigest();return json.loads(raw)
    def write(name,data):
        (output/name).write_text(json.dumps(data,indent=2,sort_keys=True,default=exact_json)+'\n')
    candidates=read('receipts/sequence_recovery/results.json')['oeis_scan']['candidates']
    rows=[];groups=defaultdict(list);initial_order=canonical_order=value_checks=subsequence_checks=0
    for row in candidates:
        model=Recurrence(tuple(map(Q,row['coefficients'])),tuple(map(Q,row['initial'])))
        n=model.order;h=[[int(i==0) for i in range(n)]];a=companion(model)
        r=witness_resolvent(a,model.initial,h);assert verify_resolvent(r)
        result=r['outputs'][0];p,q=reduced_fraction(*model.generating_function())
        assert (p,q)==(result['numerator'],result['denominator'])
        key=(p,q);groups[key].append(row['id']);initial_order+=n;canonical_order+=result['recurrence_order']
        for i in (0,1,2,10,50,100):assert resolvent_value(r,i)==model.nth(i);value_checks+=1
        samples=[]
        for offset in (0,1):
            sample=subsequence_resolvent(a,model.initial,h,offset=offset,step=2)
            for i in (0,1,10,25):assert resolvent_value(sample,i)==model.nth(offset+2*i);subsequence_checks+=1
            samples.append({'offset':offset,'step':2,'certificate':sample})
        rows.append({'id':row['id'],'source_offset':row['offset'],'model_certificate':r,'parity_subsequences':samples,
            'definition_status':'supplied reconstructed model; original OEIS definition remains separate'})
    write('recurrence_resolvents.json',{'rows':rows,'canonical_identity_groups':[
        {'ids':ids,'numerator':p,'denominator':q} for (p,q),ids in sorted(groups.items())]})
    examples=[]
    for p in (2,3,5,7,11,13):
        a=[[int((i==p)!=(j==p)) for j in range(p+1)] for i in range(p+1)]
        s=[int(i==0) for i in range(p+1)];r=witness_resolvent(a,s,[s]);out=r['outputs'][0]
        assert out['numerator']==(1,0,1-p) and out['denominator']==(1,0,-p)
        assert out['recurrence_order']==3  # denominator degree two, transient at n=0
        examples.append({'parameter':p,'certificate':r,'denominator_parameter':-out['denominator'][2]})
    nil=witness_resolvent([[0,1,0],[0,0,1],[0,0,0]],[0,0,1],[[1,0,0]])
    write('witness_examples.json',{'TY_star_matrix_models':examples,'nilpotent_transient':nil,
        'source_correction':'DLP coefficient of z^2 is -p with constant-one normalization; p is its negative. Pole-only data omits the initial zero-eigenvalue transient.'})
    corpus=read('receipts/monograph_development/connection_corpus.json');repairs=[];updates=rank_losses=events=0
    for row in corpus['rows']:
        if row['measure']['status']!='EXACT_BASIS_MEASURE':continue
        base=ConnectionMeasure.from_receipt(row['measure']);m=len(base.weights)
        variants=[list(base.weights),list(base.weights),list(base.weights),[Q(0)]*m]
        variants[1][0]=2*base.weights[0]
        variants[2][0]=0;variants[2][-1]=Q(1,2)*base.weights[-1]
        for weights in variants:
            r=reweight(base,weights);assert verify_reweight(r);assert verify_measure(r['updated'])
            fresh=ConnectionMeasure(base.graph,weights).receipt()
            for key in ('status','normalizing_determinant','laplacian_inverse','transfer_kernel','edge_marginals'):
                assert r['updated'][key]==fresh[key]
            updates+=1;rank_losses+=r['updated']['status']=='RANK_DEFICIENT'
            if r['updated']['status']=='EXACT_BASIS_MEASURE':
                repaired=ConnectionMeasure.from_receipt(r['updated']);fresh_measure=ConnectionMeasure.from_receipt(fresh)
                for inc,exc in (((0,),()),((),(m-1,)),((0,),(m-1,))):
                    assert repaired.event(inc,exc)==fresh_measure.event(inc,exc);events+=1
            repairs.append({'source_row':row['source_row'],'certificate':r})
    write('graph_repairs.json',{'updates':repairs})
    large=read('receipts/monograph_development/large_connection.json');base=ConnectionMeasure.from_receipt(large['measure'])
    weights=list(base.weights);weights[0]=2;weights[10]=0
    r=reweight(base,weights);fresh=ConnectionMeasure(base.graph,weights).receipt()
    assert verify_reweight(r) and verify_measure(r['updated'])
    assert r['updated']['laplacian_inverse']==fresh['laplacian_inverse']
    write('large_graph_repair.json',{'certificate':r,'vertices':base.graph.vertices,'edges':len(weights),
        'base_inversion_dimension':base.graph.vertices,'repair_inversion_dimension':r['inversion_dimension'],
        'candidate_maximal_minor_subsets':large['candidate_maximal_minor_subsets'],'basis_enumerations':0})
    summary={'schema':'pp-witness-repairs-development/1','recurrence_models':len(rows),'canonical_GF_classes':len(groups),
        'original_total_orders':initial_order,'reduced_total_orders':canonical_order,
        'independent_value_comparisons':value_checks,'independent_parity_subsequence_comparisons':subsequence_checks,
        'graph_source_rows':len(corpus['rows']),'graph_updates':updates,'rank_losses':rank_losses,'future_events_compared':events,
        'large_graph_vertices':base.graph.vertices,'large_graph_edges':len(weights),'large_graph_repair_dimension':r['inversion_dimension'],
        'source_sha256':hashes,'execution_verified':False,'new_lean_compilations':0,
        'scope':'exact certificates for supplied rational models and finite graph measures; no OEIS definition proof or general integer-solver completion'}
    write('summary.json',summary);print(json.dumps(summary,indent=2),flush=True);return summary


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,default=ROOT/'receipts/witness_repairs')
    args=p.parse_args();build(args.output)
