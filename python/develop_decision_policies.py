"""Reproduce integrated exact policies; no timing objective or external service."""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import argparse,json
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch
from perfectpower.decision_regions import CalibrationPolicy
from perfectpower.diagnostic_programs import DiagnosticPolicy
from perfectpower.projected_populations import ProjectedPopulation
from perfectpower.policy_workbench import write_html


def save(path,value):path.write_text(encoded(value)+'\n')


def build(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    calibration=dict(matrix=[[1,1,1]],observation=[4],lower=[0]*3,upper=[4]*3,
        target_origin=[0,0,4],target_basis=[[1,0],[0,1],[-1,-1]],target_box=[0,4,0,4])
    policy=CalibrationPolicy(calibration);save(output/'calibration_policy.json',policy.evidence());write_html(policy,output/'policy_workbench.html')
    feasible=[v for v in product(range(5),repeat=3) if sum(v)==4];checks=0
    for x,y in product([Q(k,4) for k in range(17)],repeat=2):
        target=(x,y,4-x-y);costs=[sum((a-b)**2 for a,b in zip(v,target)) for v in feasible];best=min(costs)
        assert policy.decide([x,y])['minimizers']==[v for v,c in zip(feasible,costs) if c==best];checks+=1
    window_spec=dict(calibration,observation=[20],upper=[20]*3,target_origin=[9,9,2],target_box=['-1/5','1/5','-1/5','1/5'])
    window=CalibrationPolicy(window_spec);assert len(window.packet['cells'])==1
    save(output/'lazy_target_window.json',dict(specification=window_spec,policy=window.evidence(),feasible_settings=231,
        reasoning='nonnegative triples summing to 20; choose 2 separators among 22; compiler uses no candidate enumeration'))
    hypotheses={f'setting_{i}':list(c['setting']) for i,c in enumerate(policy.packet['cells'])}
    diagnostic=dict(operators=[[[1,0,0],[0,1,0],[0,0,1]]],readouts={'first':[1,0,0],'second':[0,1,0],'third':[0,0,1],'combined':[1,5,0]},
        readout_costs={'first':1,'second':2,'third':8,'combined':4},hypotheses=hypotheses)
    program=DiagnosticPolicy(diagnostic);runs=[program.run(name) for name in hypotheses]
    assert all(r['identified']==r['hypothesis'] for r in runs);assert program.packet['worst_case_cost']==3
    save(output/'diagnostic_policy.json',dict(program=program.evidence(),runs=runs,cheapest_single_complete_readout_cost=4,
        source='hypotheses are all integer settings appearing in the compiled calibration policy',reset='read each selected measurement from the original same setting'))
    n=10**50;domain=dict(kind='domain',predicate={'op':'and','args':[{'poly':[n,1],'relation':'>='},{'poly':[-n,1],'relation':'<='}]},fields={'cubic':[0,-1,0,1]})
    projection=dict(source=domain,field='cubic');p=ProjectedPopulation(projection)
    assert p.count()==2*n-1 and p.multiplicity(0)==3
    save(output/'cubic_projection.json',dict(summary=p.summary(),collision=p.evidence()['collision_geometry'],
        multiplicity_zero=p.multiplicity(0),owner_zero=p.select(p.locate(0)),sample=p.sample(12,seed=818)))
    monotone=dict(source=dict(domain,fields={'fifth':[0,1,0,0,0,1]}),field='fifth');m=ProjectedPopulation(monotone)
    assert m.count()==2*n+1;save(output/'monotone_projection.json',dict(summary=m.summary(),collision=m.evidence()['collision_geometry'],sample=m.sample(12,seed=819)))
    specs={'calibration_policy':calibration,'diagnostic_policy':diagnostic,'projected':projection}
    requests=[dict(op='register',kind=k,name=k,specification=s) for k,s in specs.items()]+[
        dict(op='call',object='calibration_policy',method='decide',args=dict(parameter=['1/2','1/2'])),
        dict(op='call',object='diagnostic_policy',method='run',args=dict(hypothesis=next(iter(hypotheses)))),
        dict(op='call',object='projected',method='multiplicity',args=dict(value=0))]
    with Catalogue(':memory:') as catalogue:
        responses=[dict(request=r,result=dispatch(catalogue,r)) for r in requests]
        assert catalogue.get('diagnostic_policy').summary()['worst_case_cost']==3
    save(output/'service_replay.json',responses)
    (output/'service_requests.jsonl').write_text('\n'.join(encoded(r) for r in requests)+'\n')
    for name,s in specs.items():save(output/(name+'_spec.json'),s)
    summary=dict(schema='pp-decision-policy-development/1',calibration_cells=len(policy.packet['cells']),calibration_contacts=len(policy.packet['contacts']),
        calibration_oracle_queries=len(policy.packet['oracle_queries']),calibration_oracle_nodes=policy.packet['oracle_nodes'],calibration_rounds=policy.packet['rounds'],
        lazy_window_feasible_settings=231,lazy_window_discovered_settings=1,lazy_window_oracle_queries=len(window.packet['oracle_queries']),
        independent_target_checks=checks,diagnostic_hypotheses=len(hypotheses),diagnostic_worst_case_cost=str(program.packet['worst_case_cost']),
        cheapest_single_complete_readout_cost=4,diagnostic_partitions=program.packet['experiment_partitions'],
        cubic_source_count=2*n+1,cubic_distinct_count=p.count(),cubic_complete_collision_pairs=3,monotone_distinct_count=m.count(),catalogue_kinds=10,
        scope='exact policies on declared bounded models; full cubic integer collision geometry and certified discrete-monotone projections; resettable noiseless minimax diagnostics; Python, no new Lean theorem')
    save(output/'summary.json',summary);print(json.dumps(summary,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='receipts/decision_policies');build(parser.parse_args().output)
