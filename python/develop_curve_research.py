"""Reproduce the exact projective, local and multivariate research corpus."""
import argparse
import json
from pathlib import Path
from perfectpower.curve_families import CurveFamily
from perfectpower.multi_curve_families import MultiCurveFamily
from perfectpower.projective_deformation import projective_deformation
from perfectpower.rational_curve_quotients import discover_rational_quotients
from perfectpower.integral_cycle_maps import simplicial_cycle_map
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch

LEGENDRE={'coefficients':[[0],[0,1],[-1,-1],[1]]}
RECIPROCAL={'coefficients':[[1],[1],[2],[3,1],[2],[1],[1]]}
def term(powers):return {'terms':[{'powers':powers,'coefficient':1}]}
def torus(nx,ny):
    index=lambda x,y:(x%nx)*ny+y%ny
    faces=[]
    for x in range(nx):
        for y in range(ny):
            a,b,c,d=index(x,y),index(x+1,y),index(x+1,y+1),index(x,y+1)
            faces.extend([[a,b,c],[a,c,d]])
    return dict(vertices=nx*ny,triangles=faces,face_orientation_signs=[1]*len(faces))


def build(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    def save(name,value):
        (output/name).write_text(encoded(value)+'\n')
    projective={
        'moving_infinity':projective_deformation({'coefficients':[[1],[0,4],[0,0,6],[0,0,0,4],[1,0,0,0,1]]}),
        'essential_quartic':projective_deformation({'coefficients':[[0,1],[1],[0],[0],[1]]})}
    save('projective_tangents.json',projective)
    specifications={
        'universal_elliptic':dict(parameters=['a','b'],coefficients=[term([0,1]),term([1,0]),0,1]),
        'two_parameter_genus_two':dict(parameters=['a','b'],coefficients=[{'terms':[{'powers':[1,0],'coefficient':1},{'powers':[0,1],'coefficient':1}]},0,0,0,0,1]),
        'three_parameter_genus_three':dict(parameters=['a','b','c'],coefficients=[{'terms':[{'powers':p,'coefficient':1} for p in ([1,0,0],[0,1,0],[0,0,1])]},0,0,0,0,0,0,1])}
    multi={}
    for name,spec in specifications.items():
        f=MultiCurveFamily(spec)
        multi[name]=dict(specification=spec,evidence=f.evidence(),deformation=f.deformation(),observable=f.observable('a'),
                         specialization=f.specialize([1]*len(f.parameters)))
        print('compiled',name,flush=True)
    save('simultaneous_deformations.json',multi)
    legendre=CurveFamily(LEGENDRE);binomial=CurveFamily({'coefficients':[[0,1],[0],[0],[0],[0],[1]]})
    local={str(p):dict(chart=legendre.local_analysis(p),jet=legendre.frobenius_jet(p,order=12,seed=[1,0],log_degree=0) if p==0 else None) for p in (0,1,'infinity')}
    local['infinity']['jet']=legendre.frobenius_jet('infinity',exponent='1/2',seed=[1,'1/2'],log_degree=0)
    local['infinity']['resonance']=legendre.frobenius_jet('infinity',exponent='-1/2',seed=[0,1],log_degree=0)
    local['fivefold']=dict(chart=binomial.local_analysis(),jet=binomial.frobenius_jet(exponent='-3/10',log_degree=0))
    save('local_execution.json',local)
    quotient=discover_rational_quotients(RECIPROCAL);save('reciprocal_quotients.json',dict(specification=RECIPROCAL,**quotient))
    generic=CurveFamily({'coefficients':[[0,1],[-1],[0],[0],[0],[1]]})
    projectors=dict(binomial=binomial.horizontal_projectors(),generic=generic.horizontal_projectors(),rational_ansatz=binomial.horizontal_projectors(degree=1,denominator=[0,1]))
    save('filtered_projectors.json',projectors)
    s,t=torus(6,3),torus(3,3);vertex_map=[(x%3)*3+y for x in range(6) for y in range(3)]
    cycles=dict(source=s,target=t,vertex_map=vertex_map,cover=simplicial_cycle_map(s,t,vertex_map),identity=simplicial_cycle_map(t,t,list(range(9))),orientation_reverse=simplicial_cycle_map(t,t,[y*3+x for x in range(3) for y in range(3)]))
    save('integral_cycle_maps.json',cycles)
    requests=[dict(op='register',kind='curve_family',specification=LEGENDRE,name='legendre'),
        dict(op='call',object='legendre',method='projective_deformation'),
        dict(op='call',object='legendre',method='local_analysis',args={'parameter':0}),
        dict(op='call',object='legendre',method='local_analysis',args={'parameter':'infinity'}),
        dict(op='call',object='legendre',method='frobenius_jet',args={'seed':[1,0],'log_degree':0}),
        dict(op='call',object='legendre',method='de_rham_pairing'),
        dict(op='register',kind='multi_curve_family',specification=specifications['universal_elliptic'],name='universal'),
        dict(op='call',object='universal',method='deformation'),
        dict(op='call',object='universal',method='observable',args={'parameter':'b'}),
        dict(op='discover_rational_quotients',specification=RECIPROCAL),
        dict(op='cycle_map',args={'source':t,'target':t,'vertex_map':list(range(9))})]
    (output/'service_requests.jsonl').write_text(''.join(encoded(dict(r,request_id=i+1))+'\n' for i,r in enumerate(requests)))
    with Catalogue(':memory:') as catalogue:
        replies=[dict(request_id=i+1,result=dispatch(catalogue,r)) for i,r in enumerate(requests)]
    save('service_replay.json',replies)
    summary=dict(schema='pp-curve-research-development/1',projective_examples=len(projective),
        multivariate_families=len(multi),parameter_counts=[len(s['parameters']) for s in specifications.values()],
        genera=[v['evidence']['genus'] for v in multi.values()],flatness_pairs=sum(len(v['evidence']['flatness']) for v in multi.values()),
        local_charts=len(local),complete_formal_jets=3,resonances_reported=1,
        reciprocal_maps=len(quotient['quotients']),reciprocal_map_degrees=[q['map_degree'] for q in quotient['quotients']],
        elliptic_observable_orders=[q['elliptic_observable']['order'] for q in quotient['quotients']],
        constant_projector_space_dimensions=[projectors[k]['linear_space_dimension'] for k in ('binomial','generic')],
        integral_cover_degree=cycles['cover']['degree'],integral_cycle_maps=3,service_requests=len(requests),persistent_object_kinds=13,
        scope='exact identities, finite formal execution and explicit simplicial topology; no inferred Jacobian decomposition, algebraic cycle marking, new kernel proof or rigorous numerical continuation')
    save('summary.json',summary);print(json.dumps(summary,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='receipts/curve_research');build(parser.parse_args().output)
