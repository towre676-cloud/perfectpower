"""Reproduce differential fields, algebraic charts and geometric sectors."""
import argparse
import json
import time
from pathlib import Path
from perfectpower import field_polynomials as F
from perfectpower.rational_functions import RationalFunction as RF
from perfectpower.differential_extensions import DifferentialExtension,EtaleAlgebra,tensor_primitive
from perfectpower.curve_families import CurveFamily
from perfectpower.symmetry_quotients import SymmetryCurve
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch

POINT={'modulus':[-256,0,0,0,3125]}
QUINTIC={'coefficients':[[0,1],[-1],[0],[0],[0],[1]]}
LEGENDRE={'coefficients':[[0],[0,1],[-1,-1],[1]]}
BINOMIAL={'coefficients':[[0,1],[0],[0],[0],[0],[1]]}
RECIPROCAL={'coefficients':[0,1,0,[0,1],0,1],'generators':[{'matrix':[[0,1],[1,0]],'y_scale':1}]}
ROOT={'parameters':['t'],'modulus':[{'terms':[{'powers':[1],'coefficient':-1}]},0,1]}


def build(output):
    output=Path(output);output.mkdir(parents=True,exist_ok=True);timings={}
    def save(name,value):(output/name).write_text(encoded(value)+'\n')
    def run(name,fn):
        start=time.monotonic();value=fn();timings[name]=time.monotonic()-start
        print('completed',name,round(timings[name],3),'seconds',flush=True);return value
    root=DifferentialExtension(ROOT)
    multi_spec={'parameters':['a','b','c'],'modulus':[
        {'terms':[{'powers':p,'coefficient':-1} for p in ([1,0,0],[0,1,0],[0,0,1])]},0,1]}
    extensions=dict(square_root=dict(specification=ROOT,evidence=root.evidence(),
        element=root.element_data([1,1]),fixed_algebra=root.fixed_algebra([[0,-1]])),
        simultaneous=dict(specification=multi_spec,evidence=DifferentialExtension(multi_spec).evidence()),
        hilbert90=EtaleAlgebra([-2,0,1]).hilbert90([0,-1],[-1]),
        tensor_distinct=tensor_primitive(EtaleAlgebra([-2,0,1]),EtaleAlgebra([-3,0,1])),
        tensor_repeated=tensor_primitive(EtaleAlgebra([-2,0,1]),EtaleAlgebra([-2,0,1])))
    save('differential_extensions.json',extensions)
    f=CurveFamily(QUINTIC);l=CurveFamily(LEGENDRE);b=CurveFamily(BINOMIAL)
    local=run('algebraic_local_execution',lambda:dict(
        quintic_all_finite=f.algebraic_degenerations(order=6),
        legendre_all_finite=l.algebraic_degenerations(order=6),
        quintic_node_branches=f.node_branches(POINT,order=8),
        quintic_logarithmic_jet=f.resonant_frobenius(POINT,order=6,seed=[1,0,0,0]),
        legendre_infinity_resonance=l.resonant_frobenius('infinity',order=12,exponent='-1/2',seed=[0,1]),
        legendre_ramified=l.algebraic_local_chart(0,order=6,ramification=3)))
    save('algebraic_local_execution.json',local)
    ramified=run('ramified_smooth_models',lambda:dict(binomial_zero=b.ramified_scaling_chart(),binomial_infinity=b.ramified_scaling_chart('infinity'),
        algebraic_point=CurveFamily({'coefficients':[[1,0,1],[0],[0],[0],[0],[1]]}).ramified_scaling_chart({'modulus':[1,0,1]})))
    save('ramified_smooth_models.json',ramified)
    specs={
        'genus_two_plus':RECIPROCAL,
        'genus_two_minus':{**RECIPROCAL,'generators':[{'matrix':[[0,1],[1,0]],'y_scale':-1}]},
        'genus_three_elliptic':{'coefficients':[0,1,0,[0,1],0,[0,1],0,1],'generators':[{'matrix':[[0,1],[1,0]],'y_scale':1}]},
        'genus_three_genus_two':{'coefficients':[0,1,0,[0,1],0,[0,1],0,1],'generators':[{'matrix':[[0,1],[1,0]],'y_scale':-1}]},
        'even_sextic':{'coefficients':[1,0,2,0,[0,1],0,1],'generators':[{'matrix':[[-1,0],[0,1]],'y_scale':1}]},
        'order_three_mobius':{'coefficients':[0,-1,'-25/6','-10/3','5/6',1],'generators':[{'matrix':[[0,-1],[1,1]],'y_scale':-1}]},
        'cyclotomic_order_five':{'coefficients':[1,0,0,0,0,1],'coefficient_extension':[1,1,1,1,1],
            'generators':[{'matrix':[[{'algebra_coefficients':[0,1]},0],[0,1]],'y_scale':1}]}}
    center=RF([2]);z=[-center,RF([1])];t=RF([0,1])
    translated=F.add(F.add(F.power(z,5),F.scale(F.power(z,3),t)),z)
    specs['conjugated_reciprocal']={'coefficients':[a.packet() for a in translated],
        'generators':[{'matrix':[[2,-3],[1,-2]],'y_scale':1}]}
    quotients={};instances={}
    for name,spec in specs.items():
        def execute():
            curve=SymmetryCurve(spec);instances[name]=curve;q=curve.quotient()
            return dict(specification=spec,evidence=curve.evidence(),quotient=q,
                observable=curve.observable('quotient') if q['target_genus'] else None)
        quotients[name]=run(name,execute)
        save('symmetry_quotients.json',quotients)
    decompositions={name:run(name+'_jacobian',instances[name].involution_decomposition) for name in ('genus_two_plus','genus_three_elliptic')}
    save('jacobian_isogenies.json',decompositions)
    obstruction=run('arithmetic_projector_obstructions',b.cyclic_projector_obstruction)
    save('arithmetic_projector_obstructions.json',obstruction)
    requests=[
        dict(op='register',kind='differential_extension',specification=ROOT,name='sqrt_t'),
        dict(op='call',object='sqrt_t',method='evidence'),
        dict(op='call',object='sqrt_t',method='element_data',args={'coefficients':[1,1]}),
        dict(op='call',object='sqrt_t',method='fixed_algebra',args={'images':[[0,-1]]}),
        dict(op='register',kind='differential_extension',specification={'modulus':[-2,0,1]},name='sqrt_two'),
        dict(op='call',object='sqrt_two',method='hilbert90',args={'image':[0,-1],'element':[-1]}),
        dict(op='tensor_primitive',args={'left':{'modulus':[-2,0,1]},'right':{'modulus':[-3,0,1]}}),
        dict(op='register',kind='curve_family',specification=QUINTIC,name='quintic'),
        dict(op='call',object='quintic',method='algebraic_local_chart',args={'parameter':POINT,'order':3}),
        dict(op='call',object='quintic',method='algebraic_degenerations',args={'order':3}),
        dict(op='call',object='quintic',method='node_branches',args={'parameter':POINT,'order':4}),
        dict(op='call',object='quintic',method='resonant_frobenius',args={'parameter':POINT,'order':3,'seed':[1,0,0,0]}),
        dict(op='register',kind='curve_family',specification=LEGENDRE,name='legendre'),
        dict(op='call',object='legendre',method='resonant_frobenius',args={'parameter':'infinity','order':6,'exponent':'-1/2','seed':[0,1]}),
        dict(op='register',kind='curve_family',specification=BINOMIAL,name='binomial'),
        dict(op='call',object='binomial',method='ramified_scaling_chart'),
        dict(op='call',object='binomial',method='cyclic_projector_obstruction'),
        dict(op='register',kind='symmetry_curve',specification=RECIPROCAL,name='reciprocal'),
        dict(op='call',object='reciprocal',method='evidence'),
        dict(op='call',object='reciprocal',method='projectors'),
        dict(op='call',object='reciprocal',method='quotient'),
        dict(op='call',object='reciprocal',method='observable',args={'sector':'quotient'}),
        dict(op='call',object='reciprocal',method='involution_decomposition')]
    (output/'service_requests.jsonl').write_text(''.join(encoded(dict(r,request_id=i+1))+'\n' for i,r in enumerate(requests)))
    def replay():
        with Catalogue(':memory:') as catalogue:return [dict(request_id=i+1,result=dispatch(catalogue,r)) for i,r in enumerate(requests)]
    replies=run('service_replay',replay);save('service_replay.json',replies)
    summary=dict(schema='pp-algebraic-curve-development/1',persistent_object_kinds=15,
        parameter_derivations=3,mixed_derivation_pairs=3,tensor_models=2,
        finite_algebraic_degeneration_roots=local['quintic_all_finite']['covered_roots']+local['legendre_all_finite']['covered_roots'],
        nodal_branch_order=8,resonance_orders_resolved=local['legendre_infinity_resonance']['positive_resonances_resolved'],
        complete_resonant_jet_order=12,ramified_smooth_models=len(ramified),
        symmetry_quotients=len(quotients),group_orders=[q['evidence']['group_order'] for q in quotients.values()],
        quotient_genera=[q['quotient']['target_genus'] for q in quotients.values()],
        geometric_projector_ranks=[q['quotient']['projector']['rank'] for q in quotients.values()],
        quotient_observable_orders=[q['observable']['order'] for q in quotients.values() if q['observable']],
        jacobian_isogeny_degrees=[v['isogeny_degree'] for v in decompositions.values()],
        rational_betti_obstructions=sum(c['status']=='RATIONAL_BETTI_OBSTRUCTION' for c in obstruction['checks']),
        service_requests=len(requests),
        scope='exact finite etale differential arithmetic, local formal execution and actual finite-action quotients; general stable reduction, automatic integral markings and arbitrary Hodge/correspondence searches remain open')
    save('summary.json',summary);save('timings.json',timings);print(json.dumps(summary,indent=2),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',default='receipts/algebraic_curve_extensions');build(parser.parse_args().output)
