"""Reproduce polynomial explanations, collision geometry and elliptic reduction."""
import argparse
import json
from pathlib import Path
from fractions import Fraction as Q
from perfectpower.curve_families import CurveFamily
from perfectpower.elliptic_quotients import EllipticQuotientFamily,discover_elliptic_quotients,translated_even_specification
from perfectpower.rational_functions import RationalFunction as RF
from perfectpower import field_polynomials as F
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch
from perfectpower.structure_workbench import write_workbench


def save(path,value):path.write_text(encoded(value)+'\n')
def pair(z):return [float(z.real),float(z.imag)]


def build(output):
    import numpy as np
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    specs={name:dict(coefficients=[[0,1],[-1]]+[[0]]*(m-2)+[[1]]) for name,m in [('cubic',3),('quintic',5),('septic',7)]}
    specs['factored']=dict(coefficients=[[0,2,-1],[0,1],[-2,1],[-1,-1],[0],[1]])
    specs['mixed']=dict(coefficients=[[-2,0,1],[-3],[0],[1]])
    families={name:CurveFamily(spec) for name,spec in specs.items()}
    structural={name:dict(specification=specs[name],deformation=f.deformation(),root_motion=f.root_motion(),collisions=f.collisions()) for name,f in families.items()}
    save(output/'deformations_and_nodes.json',structural)
    scaling={}
    for m in (3,5,7):
        f=CurveFamily(dict(coefficients=[[0,1]]+[[0]]*(m-1)+[[1]]))
        scaling[str(m)]=dict(deformation=f.deformation(),observable=f.observable())
    t=RF([0,1]);polynomial=F.add(F.power([-t,RF([1])],5),[RF([1,1])])
    translated=CurveFamily(dict(coefficients=[list(map(str,a.n)) for a in polynomial]))
    scaling['translated_quintic']=dict(specification=translated.specification,deformation=translated.deformation(),
        centered_observable=translated.observable(translated.deformation()['scaling_explanation']['centered_differential_rows'][1]))
    save(output/'coordinate_scaling.json',scaling)
    quotient_spec=translated_even_specification(2,-1,[1,1],[0,1])
    quotient=EllipticQuotientFamily(quotient_spec)
    varying=EllipticQuotientFamily(translated_even_specification([2,1],[1,1],[1,0,1],['1/3','1/2']))
    save(output/'elliptic_quotients.json',dict(translated=dict(specification=quotient_spec,evidence=quotient.evidence(),
        first_observable=quotient.observable(),second_observable=quotient.observable('second')),
        varying=dict(specification=varying.specification,evidence=varying.evidence())))
    discovery_specs=dict(translated=quotient_spec,
        isolated=dict(coefficients=[[1],[0],[0],[0,1],[0],[0],[1]]),
        absent=dict(coefficients=[[1],[1],[0],[0],[0],[0],[1]]))
    save(output/'symmetry_discovery.json',{name:dict(specification=spec,analysis=discover_elliptic_quotients(spec)) for name,spec in discovery_specs.items()})
    images=[quotient.point_image(1,2,2),quotient.point_image(0,0,1)]
    lifts=[quotient.rational_lifts(1,1,2),quotient.rational_lifts(1,1,2,'second'),quotient.rational_lifts(0,0,0,'second')]
    half=EllipticQuotientFamily(translated_even_specification(2,-1,[1,1],[0,'1/2']))
    save(output/'rational_lifts.json',dict(images=images,lifts=lifts,nonintegral_lifts=half.rational_lifts(3,0,2),
        scope='complete rational fibres over declared quotient points, with original-coordinate integrality retained'))
    period=EllipticQuotientFamily(translated_even_specification(0,-1,[-1,1],[0,1]));periods={};errors=[]
    path=[str(Q(k,200)) for k in range(21)]
    for sector,mark in [('first',dict(center=['-2/3',0],radius='1')),('second',dict(center=['7/8',0],radius='4/5'))]:
        matrix=period.period_path(path,mark,sector=sector)['continuation']
        scalar=period.period_path([path[0],path[-1]],mark,sector=sector,mode='scalar')['continuation']
        direct=period._sector(sector).marked_period(path[-1],mark)
        error=dict(matrix_vs_direct=max(abs(complex(*a)-complex(*b)) for a,b in zip(matrix['trajectory'][-1]['state'],direct['period_vector'])),
            matrix_vs_scalar=abs(complex(*matrix['trajectory'][-1]['observable'])-complex(*scalar['trajectory'][-1]['observable'])))
        assert max(error.values())<1e-8
        periods[sector]=dict(operator=period.observable(sector),matrix=matrix,scalar=scalar,direct=direct,errors=error);errors.append(dict(sector=sector,**error))
    save(output/'quotient_periods.json',dict(specification=period.specification,sectors=periods))
    requests=[dict(op='register',kind='curve_family',name='quintic',specification=specs['quintic']),
        dict(op='call',object='quintic',method='deformation'),dict(op='call',object='quintic',method='root_motion'),
        dict(op='call',object='quintic',method='collisions'),dict(op='construct_quotient',args=dict(A=2,B=-1,C=[1,1],center=[0,1])),
        dict(op='discover_quotients',specification=discovery_specs['isolated']),
        dict(op='register',kind='elliptic_quotient',name='split',specification=quotient_spec),
        dict(op='call',object='split',method='observable',args=dict(sector='second')),
        dict(op='call',object='split',method='point_image',args=dict(parameter=1,x=2,y=2)),
        dict(op='call',object='split',method='rational_lifts',args=dict(parameter=1,u=1,v=2,sector='second'))]
    with Catalogue(':memory:') as catalogue:responses=[dict(request=r,result=dispatch(catalogue,r)) for r in requests]
    save(output/'service_replay.json',responses)
    (output/'service_requests.jsonl').write_text('\n'.join(encoded(r) for r in requests)+'\n')
    iso=CurveFamily(dict(coefficients=[[0,1],[0],[0],[0],[0],[1]]));cases={}
    configurations=[('quintic',families['quintic'],[Q(k,120) for k in range(61)]),
        ('scaling',iso,[Q(1,4)+Q(k,40) for k in range(61)]),('quotient',quotient,[Q(-1,5)+Q(k,50) for k in range(61)])]
    for name,f,parameters in configurations:
        velocities=[RF.parse(a) for a in f.root_motion()['velocity']];rows=[]
        for parameter in parameters:
            coefficients=[a.evaluate(parameter) for a in f.f]
            roots=sorted(map(complex,np.roots(list(reversed(coefficients)))),key=lambda z:(round(z.real,10),z.imag))
            speed=[sum(a.evaluate(parameter)*z**i for i,a in enumerate(velocities)) for z in roots]
            if name=='scaling':
                shape=[z/float(parameter)**.2 for z in roots];shape_speed=[v/float(parameter)**.2-z/(5*float(parameter)**1.2) for z,v in zip(roots,speed)]
            elif name=='quotient':shape=[z-float(parameter) for z in roots];shape_speed=[v-1 for v in speed]
            else:shape,shape_speed=roots,speed
            rows.append(dict(parameter=str(parameter),roots=list(map(pair,roots)),velocities=list(map(pair,speed)),shape_roots=list(map(pair,shape)),shape_velocities=list(map(pair,shape_speed))))
        if name=='quintic':
            explanation=structural['quintic']['collisions'];operator=f.observable()['polynomial_operator'];radius=5**(-.25)
            label='Genuine deformation · four exact nodal collision parameters';shape_label='Shape coordinates equal original coordinates in this example.'
            collision_roots=[[radius,0],[-radius,0],[0,radius],[0,-radius]];polynomial_label='y² = x⁵ − x + t';title='Shape-changing quintic'
        elif name=='scaling':
            explanation=f.deformation()['scaling_explanation'];operator=f.observable()['polynomial_operator'];label='Coordinate-only deformation · first-order scaling law'
            shape_label='u = x / t^(1/5): the five root positions remain fixed.';collision_roots=[];polynomial_label='y² = x⁵ + t';title='Scaling quintic'
        else:
            explanation=dict(center=f.center.packet(),maps=f.evidence()['quotient_maps'],basis=f.evidence()['basis'],residue_removal=f.evidence()['residue_removal'])
            operator=dict(first=f.observable()['operator']['polynomial_operator'],second=f.observable('second')['operator']['polynomial_operator'])
            label='Hidden translated reflection · two second-order elliptic sectors';shape_label='z = x − t: reflection pairs become centered at zero.'
            collision_roots=[];polynomial_label='y² = (x−t)⁶ + 2(x−t)⁴ − (x−t)² + 1+t';title='Translated sextic with two elliptic quotients'
        cases[name]=dict(title=title,diagnosis=label,shape_coordinate=shape_label,polynomial=polynomial_label,explanation=explanation,
            operator=operator,collision_roots=collision_roots,samples=rows,numerical_roots_certified=False)
    save(output/'root_geometry.json',cases);write_workbench(cases,output/'structure_workbench.html')
    summary=dict(schema='pp-curve-structure-development/1',structural_families=len(families),
        covered_simple_collision_roots=sum(v['collisions']['covered_simple_roots'] for v in structural.values()),
        collision_algebra_components=sum(len(v['collisions']['components']) for v in structural.values()),
        scaling_explanations=len(scaling),quotient_source_families=2,quotient_de_rham_reductions=8,
        elliptic_sectors=2,elliptic_observable_orders=[quotient.observable()['operator']['order'],quotient.observable('second')['operator']['order']],
        geometry_samples=sum(len(c['samples']) for c in cases.values()),quotient_period_samples=42,numerical_errors=errors,
        service_requests=len(requests),persistent_object_kinds=12,
        scope='exact polynomial, quotient-algebra and de Rham identities; numerical root plots and period execution are approximations; no new Lean theorem or general elliptic-cover classification')
    save(output/'summary.json',summary);print(json.dumps(summary,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='receipts/curve_structure');build(parser.parse_args().output)
