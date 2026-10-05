"""Reproduce application receipts and a local interactive geometry client.

No external services or nonstandard runtime dependencies are required.
Hardware timings vary; all arithmetic outputs have independent checks.
"""
import argparse
from collections import Counter
from pathlib import Path
from fractions import Fraction as Q
from statistics import median
from time import perf_counter_ns
import json
from perfectpower.catalogue import Catalogue, encoded
from perfectpower.populations import ExactPopulation
from perfectpower.application_objects import SequenceLibrary, InverseDesign, GraphEnsemble, GeometryWorkbench, CombinatorialDesign
from perfectpower.configuration_tuning import tune, blocked_matmul
from perfectpower.task_protocol import heldout_tasks, public_tasks, evaluate_tasks
from perfectpower.query_service import dispatch


def save(path, value):
    path.write_text(json.dumps(json.loads(encoded(value)), indent=2)+'\n')


def build(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    population=dict(kind='domain', predicate={'op':'and','args':[{'poly':[-1,1],'relation':'>='},{'poly':[-4,1],'relation':'<='}]},
                    fields={'row_block':[0,0,0,1],'column_block':[0,0,1],'tile_elements':[0,0,0,0,0,1]})
    sequence=dict(operator=[[1,1],[1,0]],seed=[0,1],readouts={'fibonacci':[1,0],'next_fibonacci':[1,1],'lucas':[1,2]})
    inverse=dict(matrix=[[1,1,1],[2,0,1]],metric=[[2,0,0],[0,1,0],[0,0,3]])
    graph=dict(vertices=2,edges=[[0,1,0],[0,1,1],[0,0,1],[1,1,1]],power=2,weights=[1,2,3,1])
    geometry=dict(coefficients=[0,-1,0,1],panels={
        'branch_0':dict(chart='branch',branch=0,box=['-1/4','1/4','-1/4','1/4'],lower_scale='99/100',upper_scale='103/100',reference_density=4,depth=2),
        'infinity':dict(chart='infinity',box=['-1/4','1/4','-1/4','1/4'],lower_scale='99/100',upper_scale='103/100',reference_density=4,depth=2),
        'finite':dict(chart='finite',box=[2,3,0,'1/4'],lower_scale='1/6',upper_scale='1/2',depth=2)})
    combinatorial=dict(expression={'kind':'binomial','width':2},degree=2)
    specs=dict(population=population,sequence=sequence,inverse=inverse,graph=graph,geometry=geometry,combinatorial=combinatorial)
    for kind,spec in specs.items():save(output/(kind+'_spec.json'),spec)
    # Definitions, not megabytes of materialized objects, survive restart.
    database=output/'applications.sqlite'
    if database.exists():database.unlink()
    with Catalogue(str(database)) as catalogue:
        registrations=[catalogue.register(kind,spec,kind) for kind,spec in specs.items()]
        service_calls=[dict(op='call',object='population',method='select',args={'rank':2}),
            dict(op='call',object='sequence',method='terms',args={'index':1000000000000000,'modulus':1000000007}),
            dict(op='call',object='inverse',method='solve',args={'observation':[20,18],'target':['9/2','25/4','35/4']}),
            dict(op='call',object='graph',method='sample',args={'size':8,'seed':22,'excluded':[0]}),
            dict(op='call',object='geometry',method='segment',args={'panel':'branch_0','start':['-1/4',0],'end':['1/4',0]}),
            dict(op='call',object='combinatorial',method='sizes',args={'bound':10**100})]
        responses=[dict(request=r,result=dispatch(catalogue,r)) for r in service_calls]
        save(output/'service_replay.json',dict(registrations=registrations,responses=responses,compilations=catalogue.compilations))
        definitions=catalogue.list()
    with Catalogue(str(database)) as catalogue:
        assert catalogue.list()==definitions
        assert catalogue.get('population').count()==4
    # SQLite bytes are platform-specific; commit the portable definitions and
    # transcript instead of this generated database.
    database.unlink()
    (output/'service_requests.jsonl').write_text('\n'.join(encoded(dict(op='register',kind=k,specification=s,name=k)) for k,s in specs.items())+'\n'+'\n'.join(encoded(r) for r in service_calls)+'\n')

    s=SequenceLibrary(sequence);a,b=0,1;reference=[]
    for index in range(40):
        values=s.terms(index);assert values==dict(fibonacci=a,next_fibonacci=a+b,lucas=a+2*b)
        reference.append(dict(index=index,values=values));a,b=a+b,a
    save(output/'sequence_library.json',dict(definition=sequence,summary=s.summary(),terms=reference,
        subsequence=s.subsequence(5,3),identity=s.compare(s,'fibonacci','fibonacci'),
        experiment=s.experiment([0,1],[1,0],readout_costs=[5,1,2]),
        long_index_modular=s.terms(10**15,modulus=1000000007),reference='literal two-state iteration for indices 0..39'))

    design=InverseDesign(inverse); result=design.solve([20,18],['9/2','25/4','35/4'])
    target=list(map(Q,['9/2','25/4','35/4']))
    brute=[]
    for first in range(-30,31):
        third=18-2*first;second=20-first-third
        energy=sum(w*(Q(v)-t)**2 for w,v,t in zip([2,1,3],[first,second,third],target))
        brute.append((energy,(first,second,third)))
    best=min(e for e,_ in brute)
    assert best==result['minimum_energy'] and set(result['minimizers'])=={v for e,v in brute if e==best}
    save(output/'integer_calibration.json',dict(model='three signed integer actuator increments, two exact linear observations',result=result,
        independent_bounded_reference='eliminate two variables, scan first increment -30..30; global completeness comes from the exact optimizer'))

    ensemble=GraphEnsemble(graph)
    derived, repair=ensemble.with_weights([1,2,0,1])
    save(output/'graph_ensemble.json',dict(definition=graph,measure=ensemble.measure.receipt(),
        unconditional=ensemble.sample(32,seed=71),conditioned=ensemble.sample(32,seed=71,excluded=[0]),
        repaired=repair,repaired_samples=derived.sample(8,seed=71)))
    workbench=GeometryWorkbench(geometry);workbench.write_html(output/'geometry_workbench.html',9)
    save(output/'geometry_panels.json',dict(packets=workbench.packets,grids={name:workbench.grid(name,5) for name in workbench.packets}))
    combo=CombinatorialDesign(combinatorial)
    save(output/'combinatorial_sizes.json',dict(gamma=combo.gamma(interval=[0,100]),sizes=combo.sizes(10**100),
        filtered=combo.sizes(10**100,[['root',7,0]]),first_sizes=[combo.select_size(i) for i in range(12)]))

    curves=dict(kind='curve',left=[0,0,2],right=[0,0,0,3],predicate={'expr':f'y-{6*10**12}','relation':'<='})
    tasks=heldout_tasks(ExactPopulation(curves),256,seed=511,family='signed_square_cube')
    save(output/'heldout_private.json',tasks)
    for split in ('train','validation','test'):
        (output/(split+'_tasks.jsonl')).write_text('\n'.join(encoded(t) for t in public_tasks(tasks,split))+'\n')
    predictions={t['task_id']:t['answer'] for t in tasks['tasks'] if t['split']=='test'}
    save(output/'evaluation_replay.json',dict(evaluation=evaluate_tasks(tasks,predictions),
        provenance='oracle replay of exact answers, not measured agent performance'))

    # Actual 32x32 integer matrix multiplication, no mocked timing objective.
    n=32;left=[[(i*17+k*5)%11-5 for k in range(n)] for i in range(n)]
    right=[[(k*7+j*3)%13-6 for j in range(n)] for k in range(n)]
    def conventional():return [[sum(a*b for a,b in zip(row,col)) for col in zip(*right)] for row in left]
    expected=conventional()
    tuning=tune(ExactPopulation(population),lambda c:blocked_matmul(left,right,c['row_block'],c['column_block']),expected,repeats=7,warmups=1,seed=61)
    baseline=[]
    for _ in range(7):
        start=perf_counter_ns();value=conventional();baseline.append(perf_counter_ns()-start);assert value==expected
    tuning.update(workload=dict(kernel='32x32 exact integer matrix product', candidate_semantics='row tile n^3, column tile n^2, tile capacity n^5, n=1..4'),
        conventional=dict(kernel='Python dot products using sum/zip',trials_ns=baseline,median_ns=median(baseline)),
        comparison_scope='Different Python loop organizations; conventional baseline timed separately. Timings do not establish compiled-kernel or hardware speedup.')
    save(output/'measured_tuning.json',tuning)
    summary=dict(schema='pp-applications-development/1',catalogue_kinds=len(specs),sequence_reference_indices=40,
        curve_tasks=len(tasks['tasks']),task_splits=dict(Counter(t['split'] for t in tasks['tasks'])),
        geometry_panels=3,graph_samples=72,tuning_candidates=4,timed_kernel_trials=28,
        winner_ranks=[r['rank'] for r in tuning['winners']],measured_minimum_median_ns=tuning['minimum_median_ns'],
        conventional_median_ns=median(baseline),portable_receipts=True)
    save(output/'summary.json',summary);print(json.dumps(summary,indent=2))


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',default='receipts/applications');build(p.parse_args().output)
