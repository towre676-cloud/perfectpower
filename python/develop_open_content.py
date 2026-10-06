"""Reproduce the uncapped open-content development release.

Exact receipts are deterministic; benchmark timings describe this host only.
Run from the checkout: PYTHONPATH=python python python/develop_open_content.py
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from math import factorial
from pathlib import Path
import json
import gzip
import re
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch
from perfectpower.application_objects import SequenceLibrary,InverseDesign,GraphEnsemble,GeometryWorkbench
from perfectpower.projected_populations import ProjectedPopulation,symbolic_join
from perfectpower.populations import ExactPopulation
from perfectpower.factorial_library import FactorialLibrary
from perfectpower.compiled_tuning import benchmark,compatible_tiles
from perfectpower.task_protocol import heldout_families,public_tasks,solve_public_tasks,evaluate_tasks
from perfectpower.flavor_identifiability import stationarity_space,allowed_linear_response,interaction_obligations
from perfectpower.cyclotomic_real import verify_decision
from perfectpower.bounded_inverse import verify_bounded_design
from perfectpower.chart_transitions import verify_transition

ROOT=Path(__file__).resolve().parents[1]


def save(path,value):
    data=(encoded(value)+'\n').encode()
    if path.name in {'algebraic_graphs.json','flavor_identifiability.json','nonlinear_factorial_library.json'}:
        path.with_suffix(path.suffix+'.gz').write_bytes(gzip.compress(data,compresslevel=9,mtime=0))
    else:path.write_bytes(data)


def source_review():
    machines={
        'fib':SequenceLibrary(dict(operator=[[0,1],[1,1]],seed=[0,1],readouts={'fibonacci':[1,0],'lucas':[-1,2]})),
        'pell':SequenceLibrary(dict(operator=[[0,1],[1,2]],seed=[0,1],readouts={'pell':[1,0]}))}
    definitions=[('A000045','fib','fibonacci',0),('A000032','fib','lucas',0),('A000204','fib','lucas',1),('A000129','pell','pell',0)]
    review=[]
    for identifier,machine,readout,offset in definitions:
        path=ROOT/'data'/'oeis'/'seq'/identifier[:4]/(identifier+'.seq');text=path.read_text()
        terms=[int(x) for line in text.splitlines() if line[:2] in ('%S','%T','%U') for x in line.split(' ',2)[2].split(',') if x]
        computed=[machines[machine].terms(i+offset)[readout] for i in range(len(terms))]
        assert computed==terms
        review.append(dict(identifier=identifier,source=f'https://oeis.org/{identifier}',snapshot=str(path.relative_to(ROOT)),
            sha256=sha256(path.read_bytes()).hexdigest(),machine=machine,readout=readout,offset=offset,
            checked_terms=len(terms),terms=terms,definition_review='explicit recurrence, initial values and offset; prefix equality is an independent check, not an identity inference'))
    return dict(definitions=review,machines={name:machine.summary() for name,machine in machines.items()})


def inventory():
    paths=[ROOT/'docs'/n for n in ('OPEN_FRONTS.md','OPEN_PROBLEMS.md','FRONTIER_PLAN.md','M22_TRANSPORT_INTERACTIONS.md')]
    notes=[]
    for path in paths:
        content=path.read_text();paragraphs=re.split(r'\n\s*\n',content)
        cursor=0
        for paragraph in paragraphs:
            start=content.find(paragraph,cursor);cursor=start+len(paragraph)
            if re.search(r'\b(open|remain\w*|unresolved|needed|necessary|obstruction|conjecture\w*|hypothes\w*)\b',paragraph,re.I):
                notes.append(dict(source=str(path.relative_to(ROOT)),line=content[:start].count('\n')+1,
                    text=paragraph,status='SOURCE_NOTE_REQUIRES_CURRENT_PROOF_REVIEW'))
    return dict(schema='pp-open-source-inventory/1',sources=[dict(path=str(p.relative_to(ROOT)),sha256=sha256(p.read_bytes()).hexdigest(),
        full_text=p.read_text()) for p in paths],notes=notes,
        semantics='Full historical research notes retained. Keyword extraction identifies claims to review, not independent verified open problems. Current application closure and precise limitations are in DIRECT_USE_BUILD_ROADMAP.md.')


def build(output,*,repeats=7):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    sequence=dict(operator=[[1,1],[1,0]],seed=[0,1],readouts={'expensive':[1,0],'cheap':[0,1]})
    s=SequenceLibrary(sequence)
    experiment=dict(stored_witness=s.witness_experiment([1,0],[0,0],readout_costs=[100,1]),
        global_optimum=s.experiment([1,0],[0,0],readout_costs=[100,1]))
    assert experiment['stored_witness']['cost']==100 and experiment['global_optimum']['cost']==2
    save(output/'global_experiment.json',experiment);save(output/'reviewed_sequences.json',source_review())

    inverse=dict(matrix=[[1,1,1],[2,0,1]],metric=[[2,0,0],[0,1,0],[0,0,3]])
    inequalities=[dict(coefficients=[1,-1,0],relation='>=',rhs=-4),dict(coefficients=[0,1,1],relation='<=',rhs=17)]
    bounded=InverseDesign(inverse).solve_box([20,18],['9/2','25/4','35/4'],[0,0,0],[15,15,15],inequalities)
    assert verify_bounded_design(json.loads(encoded(bounded)))
    candidates=[(a,20-a-(18-2*a),18-2*a) for a in range(16)]
    candidates=[v for v in candidates if all(0<=x<=15 for x in v) and v[0]-v[1]>=-4 and v[1]+v[2]<=17]
    target=list(map(Q,['9/2','25/4','35/4']))
    energy=lambda v:sum(w*(x-t)**2 for w,x,t in zip([2,1,3],v,target))
    assert bounded['minimum_energy']==min(map(energy,candidates))
    save(output/'bounded_calibration.json',dict(result=bounded,independent_candidates=candidates,
        use='closest nonnegative bounded integer actuator settings satisfying exact observations and inequality coupling'))

    graph=dict(vertices=1,edges=[[0,0,1],[0,0,2],[0,0,3]],power=5,weights=[1,2,3])
    graphs={}
    for order in range(2,65):
        ensemble=GraphEnsemble(dict(graph,power=order));packet=ensemble.sample(8,seed=1700+order)
        assert all(verify_decision(d['comparison']) for row in packet['samples'] for d in row['decisions'])
        graphs[str(order)]=packet
    save(output/'algebraic_graphs.json',dict(samples=graphs,orders=63,total_samples=504,
        scope='exact specified rank-one gain-graph ensembles; every decision recomputed from rational analytic bounds'))

    geometry=dict(coefficients=[0,-1,0,1],panels={
        'finite':dict(chart='finite',box=[2,3,'-1/4','1/4'],lower_scale='1/6',upper_scale='1/2',depth=3),
        'branch':dict(chart='branch',branch=0,box=['3/2','8/5','-1/100','1/100'],lower_scale='1/2',upper_scale=2,depth=3),
        'infinity':dict(chart='infinity',box=['3/5','13/20','-1/100','1/100'],lower_scale=1,upper_scale=3,depth=3)})
    workbench=GeometryWorkbench(geometry)
    transitions={name:workbench.transition(name,'finite') for name in ('branch','infinity')}
    assert all(p['complete'] and verify_transition(p) for p in transitions.values())
    save(output/'compatible_geometry.json',dict(panels=workbench.packets,transitions=transitions,
        transports={name:workbench.transport(name,'finite',point) for name,point in [('branch',['31/20',0]),('infinity',['5/8',0])]},
        scope='certified compatible overlaps, not a global atlas or geodesic solver'))
    workbench.write_html(output/'geometry_workbench.html',5)

    bound=10**50
    source=dict(kind='domain',predicate={'op':'and','args':[{'poly':[bound,1],'relation':'>='},{'poly':[-bound,1],'relation':'<='}]},fields={'square':[0,0,1]})
    projected=dict(source=source,field='square');p=ProjectedPopulation(projected)
    join=symbolic_join(ExactPopulation(source),ExactPopulation(source),'square','square')
    assert p.count()==bound+1 and join.count()==4*bound+1
    save(output/'distinct_values_and_join.json',dict(source_cardinality=2*bound+1,projection=p.summary(),
        uniform_distinct_sample=p.sample(16,seed=411),multiplicities={str(v):p.multiplicity(v) for v in (0,1,4,bound**2)},
        join=join.summary(),join_sample=join.sample(16,seed=411),semantics='projection uniform over distinct values; join retains every original-parameter pair'))

    bober=json.loads((ROOT/'data/gamma_bober52.json').read_text())
    factorial_spec=dict(families={f'bober_{row["table_line"]:02d}':dict(numerator=row['numerator'],denominator=row['denominator']) for row in bober['rows']})
    library=FactorialLibrary(factorial_spec);terms=library.terms(12)
    for name,definition in factorial_spec['families'].items():
        for n,value in enumerate(terms[name]):
            top=__import__('math').prod(factorial(c*n) for c in definition['numerator'])
            bottom=__import__('math').prod(factorial(c*n) for c in definition['denominator'])
            assert Q(value)==Q(top,bottom)
    save(output/'nonlinear_factorial_library.json',dict(source=bober['source'],source_data_sha256=sha256((ROOT/'data/gamma_bober52.json').read_bytes()).hexdigest(),
        summary=library.summary(),small_terms=terms,huge_residues=[library.residues(10**100,p,d) for p,d in [(7,3),(17,2)]],
        reference='all 624 small terms independently checked using literal factorial ratios; residues strip p factors before division'))

    families=[]
    for i,(left,right) in enumerate([(2,3),(3,5),(2,5),(3,4),(2,7),(4,5),(3,7),(4,7)]):
        families.append(dict(family=f'power_{left}_{right}',split='train' if i<4 else 'validation' if i<6 else 'test',
            specification=dict(kind='curve',left=[0]*left+[1],right=[0]*right+[1],predicate={'expr':f'x*x+y*y-{10**24}','relation':'<='})))
    tasks=heldout_families(families,size_per_family=64,seed=619);save(output/'heldout_private.json',tasks)
    for split in ('train','validation','test'):
        (output/(split+'_tasks.jsonl')).write_text('\n'.join(encoded(t) for t in public_tasks(tasks,split))+'\n')
    solver=solve_public_tasks(public_tasks(tasks,'test'));evaluation=evaluate_tasks(tasks,solver['predictions'])
    assert evaluation['accuracy']=='1'
    save(output/'public_solver_evaluation.json',dict(solver=solver,evaluation=evaluation))

    specs=dict(population=source,projected=projected,sequence=sequence,inverse=inverse,graph=graph,geometry=geometry,
        combinatorial=dict(expression={'kind':'binomial','width':2},degree=2),factorial=factorial_spec)
    calls=[dict(op='call',object='projected',method='count'),dict(op='call',object='factorial',method='residues',args=dict(index=10**100,prime=7,depth=3)),
        dict(op='call',object='sequence',method='experiment',args=dict(left=[1,0],right=[0,0],readout_costs=[100,1])),
        dict(op='call',object='inverse',method='solve_box',args=dict(observation=[20,18],target=['9/2','25/4','35/4'],lower=[0]*3,upper=[15]*3,inequalities=inequalities)),
        dict(op='call',object='graph',method='sample',args=dict(size=4,seed=6)),
        dict(op='call',object='geometry',method='transport',args=dict(source='branch',target='finite',point=['31/20',0])),
        dict(op='call',object='combinatorial',method='sizes',args=dict(bound=10**100)),
        dict(op='symbolic_join',object='population',other='population',name='joined',args=dict(left_field='square',right_field='square')),
        dict(op='call',object='joined',method='count')]
    requests=[dict(op='register',kind=k,specification=v,name=k) for k,v in specs.items()]+calls
    with Catalogue(':memory:') as catalogue:responses=[dict(request=r,result=dispatch(catalogue,r)) for r in requests]
    save(output/'service_replay.json',responses)
    (output/'service_requests.jsonl').write_text('\n'.join(encoded(r) for r in requests)+'\n')
    for kind,spec in specs.items():save(output/(kind+'_spec.json'),spec)

    tuning={str(n):benchmark(n,repeats=repeats) for n in (96,192)}
    cpu=next((line.split(':',1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')),None)
    for result in tuning.values():result['environment']['cpu']=cpu
    save(output/'compiled_tuning.json',tuning)
    save(output/'flavor_identifiability.json',dict(stationarity=stationarity_space(),responses=[allowed_linear_response(lock=i) for i in (0,1)],interaction=interaction_obligations()))
    notes=inventory();save(output/'open_source_inventory.json',notes)
    summary=dict(schema='pp-open-content-development/1',catalogue_kinds=8,archive_size_limit=None,
        graph_orders=63,graph_samples=504,nonlinear_families=len(factorial_spec['families']),nonlinear_independent_term_checks=624,
        curve_tasks=len(tasks['tasks']),task_splits=dict(Counter(t['split'] for t in tasks['tasks'])),
        solver_test_accuracy=evaluation['accuracy'],compiled_candidates=compatible_tiles().count(),
        compiled_measurements={n:dict(baseline_median_ns=r['comparison']['median_ns'],best_median_ns=r['minimum_median_ns'],
            baseline_over_best=r['comparison']['baseline_over_best_median'],untiled_median_ns=r['controls']['cache_friendly_untiled']['median_ns'],
            untiled_over_best=r['controls']['cache_friendly_untiled']['baseline_over_best_median'],winner_parameters=[v['parameter'] for v in r['winners']]) for n,r in tuning.items()},
        stationarity_codimension=8,stationary_coefficient_dimension=5,source_notes_retained=len(notes['notes']),
        mathematics_status='general effective backends, global smooth geometry, kernel certification and UV flavor derivation remain open')
    save(output/'summary.json',summary);print(json.dumps(summary,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='receipts/open_content');parser.add_argument('--repeats',type=int,default=7)
    args=parser.parse_args();build(args.output,repeats=args.repeats)
