"""Reproduce exact family algebra, marked continuations and sourced arithmetic."""
import argparse
import hashlib
import json
from pathlib import Path
from fractions import Fraction as Q
from perfectpower.curve_families import CurveFamily
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch
from perfectpower.family_workbench import write_workbench

ROOT=Path(__file__).resolve().parents[1]
SPECS=dict(legendre=dict(coefficients=[[0],[0,1],[-1,-1],[1]]),
    genus_two=dict(coefficients=[[0,1],[-1],[0],[0],[0],[1]]),
    isotrivial=dict(coefficients=[[0,1],[0],[0],[0],[0],[1]]),
    genus_three=dict(coefficients=[[0,1],[-1],[0],[0],[0],[0],[0],[1]]),
    mordell=dict(coefficients=[[0,1],[0],[0],[1]]))


def save(path,value):path.write_text(encoded(value)+'\n')


def build(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True);families={name:CurveFamily(spec) for name,spec in SPECS.items()}
    for name,family in families.items():save(output/(name+'_algebra.json'),dict(specification=SPECS[name],family=family.evidence(),observable=family.observable()))
    marks=dict(legendre=dict(center='1/8',radius='1/5'),genus_two=dict(center='1/2',radius='13/20'),
        isotrivial=dict(center='4/5',radius='7/10'))
    paths=dict(legendre=[str(Q(1,4)+Q(k,80)) for k in range(21)],genus_two=[str(Q(k,100)) for k in range(21)],isotrivial=[str(1+Q(k,40)) for k in range(21)])
    cases={};numerical=[]
    for name,mark in marks.items():
        family=families[name];matrix=family.period_path(paths[name],mark);scalar=family.period_path([paths[name][0],paths[name][-1]],mark,mode='scalar')
        endpoint_mark=dict(center='1/4',radius='7/20') if name=='legendre' else mark
        direct=family.marked_period(paths[name][-1],endpoint_mark)
        errors=dict(matrix_vs_scalar=abs(complex(*matrix['trajectory'][-1]['observable'])-complex(*scalar['trajectory'][-1]['observable'])),
            matrix_vs_direct=max(abs(complex(*a)-complex(*b)) for a,b in zip(matrix['trajectory'][-1]['state'],direct['period_vector'])))
        assert max(errors.values())<1e-8
        cases[name]=dict(summary=family.summary(),observable=family.observable(),continuation=matrix,scalar=scalar,direct_endpoint=direct,errors=errors)
        numerical.append(dict(family=name,**errors))
    save(output/'marked_continuations.json',cases)
    # Actual branch-preserving parameter-loop transport, in the de Rham basis.
    loop=['1/4',['1/4','1/4'],['-1/4','1/4'],['-1/4','-1/4'],['1/4','-1/4'],'1/4']
    save(output/'legendre_monodromy.json',families['legendre'].transport(loop))
    f=families['genus_two'];weighted=f.observable([[0,1],0,0,0])
    matrix=f.period_path([0,'1/5'],marks['genus_two'],[[0,1],0,0,0]);rejections=[]
    for label,operation in [('genuine_real_collision',lambda:f.transport([0,1])),
        ('genuine_complex_collision',lambda:f.transport([0,[0,1]])),
        ('scalar_singularity_at_smooth_zero',lambda:f.period_path([0,'1/5'],marks['genus_two'],[[0,1],0,0,0],mode='scalar'))]:
        try:operation()
        except ValueError as error:rejections.append(dict(case=label,error=str(error)))
        else:raise AssertionError('expected path obstruction')
    save(output/'singularity_routes.json',dict(observable=weighted,matrix_at_smooth_zero=matrix,rejections=rejections,
        valid_complex_detour=f.transport([0,['1/4','1/4'],[1,'1/4'],1])))
    large=10**50;parameter=families['legendre'].parameter_population(-large,large)
    assert parameter['summary']['cardinality']==2*large-1
    save(output/'parameter_population.json',parameter)
    source=ROOT/'data/mordell_census.jsonl';records=[json.loads(line) for line in source.read_text().splitlines()]
    selected=[r for r in records if r['k'] in (-89,-22,-2,1,2,4)];checks=[]
    for record in selected:
        result=families['mordell'].integer_points(record['k'],-50,50)
        expected=sorted(x for x in record['x_coordinates'] if -50<=x<=50)
        assert sorted({x for x,y in result['points']})==expected
        # The Weierstrass curve discriminant is 16 times the cubic discriminant.
        assert record['discriminant']==16*families['mordell'].specialize(record['k'])['discriminant']
        checks.append(dict(k=record['k'],recorded_x_coordinates=expected,bounded_result=result))
    save(output/'sourced_mordell_specializations.json',dict(source='data/mordell_census.jsonl',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        source_records=len(records),checks=checks,scope='six sourced specializations compared on x in [-50,50]; no promotion of bounded checks to global completeness'))
    requests=[dict(op='register',kind='curve_family',name='genus_two',specification=SPECS['genus_two']),
        dict(op='call',object='genus_two',method='observable'),dict(op='call',object='genus_two',method='specialize',args=dict(parameter='1/5')),
        dict(op='call',object='genus_two',method='integer_points',args=dict(parameter=0,lower=-3,upper=3)),
        dict(op='call',object='genus_two',method='period_path',args=dict(path=[0,'1/5'],contour=marks['genus_two']))]
    with Catalogue(':memory:') as catalogue:responses=[dict(request=r,result=dispatch(catalogue,r)) for r in requests]
    save(output/'service_replay.json',responses)
    (output/'service_requests.jsonl').write_text('\n'.join(encoded(r) for r in requests)+'\n')
    write_workbench(cases,output/'family_workbench.html')
    summary=dict(schema='pp-curve-family-development/1',compiled_families=len(families),genera=[1,2,3],
        exact_reduction_identities=sum(f.dimension for f in families.values()),generic_genus_two_observable_order=4,
        isotrivial_state_dimension=4,isotrivial_observable_order=1,genus_three_observable_order=6,
        marked_comparison_families=len(cases),sampled_period_vertices=sum(len(v) for v in paths.values()),numerical_errors=numerical,
        sourced_mordell_specializations=len(checks),source_census_records=len(records),huge_parameter_population_count=2*large-1,
        exact_path_rejections=len(rejections),persistent_object_kinds=11,
        scope='exact Q(t) identities and parameter-path zero exclusions; numerical marked periods and transport; bounded integer specialization checks; no new Lean proof')
    save(output/'summary.json',summary);print(json.dumps(summary,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='receipts/curve_families');build(parser.parse_args().output)
