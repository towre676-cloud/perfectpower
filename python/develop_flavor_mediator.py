"""Reproduce the exact shared-mediator audits and numerical matching experiments."""
from pathlib import Path
from itertools import product
from math import pi,sqrt
import hashlib,json
import numpy as np
from perfectpower.flavor_mediator import (
    abelian_circuit_audit,mediator_operator_audit,alignment_basis,
    canonical_mediator,mixing_record,assignment_certificate,
    degree_eight_example,golden_squared_relation,matched_adjoint)
from perfectpower.flavor_prediction import ckm_from_depth

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/flavor_mediator'


def save(name,data):
    (OUT/name).write_text(json.dumps(data,sort_keys=True,indent=2,allow_nan=False)+'\n')


def main():
    OUT.mkdir(exist_ok=True)
    training=json.loads((ROOT/'receipts/flavor_prediction/training.json').read_text())
    u,v=training['Vus']['mean'],training['Vcb']['mean'];golden=(3-sqrt(5))/2
    save('abelian_obstruction.json',abelian_circuit_audit())
    save('shared_mediator_operators.json',mediator_operator_audit())
    save('adjoint_mediator_operators.json',mediator_operator_audit(adjoint=True))
    save('scalar_alignment_basis.json',alignment_basis())
    costs=[[[0,3,6],[5,0,2],[4,7,0]],[[4,0,3],[0,6,1],[2,5,0]],
           [[-3,4,8],[2,-5,1],[7,3,-2]],[[1]*3 for _ in range(3)]]
    save('orientation_certificates.json',{'certificates':[assignment_certificate(c) for c in costs],
        'degree_eight_capability_example':degree_eight_example(),
        'golden_observable_target':golden_squared_relation()})
    target=ckm_from_depth(golden,11*pi/30,u,v)
    transfers=[]
    for scale,mu,md in product((.1,1.,3.),(.7,1+1j),(1.2,2-.3j)):
        yu=canonical_mediator(mu*np.eye(3),scale*np.diag([.01,.1,.8]))['Y']
        yd=canonical_mediator(md*np.eye(3),scale*target@np.diag([.02,.2,.6]))['Y']
        transfers.append({'flavon_column_scale':scale,'up_mass':[float(complex(mu).real),float(complex(mu).imag)],
            'down_mass':[float(complex(md).real),float(complex(md).imag)],'observables':mixing_record(yu,yd)})
    rng=np.random.default_rng(5053901)
    lu=.2*rng.normal(size=(3,3));ld=.3*(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)))
    universal=[]
    for mu,md in ((.3,1.),(1+1j,.7-.3j),(3.,2.)):
        universal.append({'up_mass':[float(complex(mu).real),float(complex(mu).imag)],
            'down_mass':[float(complex(md).real),float(complex(md).imag)],
            'observables':mixing_record(canonical_mediator(mu*np.eye(3),lu)['Y'],canonical_mediator(md*np.eye(3),ld)['Y'])})
    save('conditional_frame_transfer.json',{'cases':transfers,'nonorthogonal_universal_mass_cases':universal,
        'universal_mass_theorem':'For L=U diag(s_i) W^dagger and M=m I, Y has the same left U with singular values |h| s_i/sqrt(|m|^2+s_i^2). Nondegenerate mass ordering is preserved.',
        'scope':'The down flavon frame is initialized from the nominated CKM chart. This verifies exact mass-independent transmission, not a symmetry derivation of that frame.'})
    cases=[];failed=[]
    for gu,gd,scale in product((0.,.1,.2),(.3,.5,.7,1.),(.1,1.,3.)):
        parameters={'gu':gu,'gd':gd,'flavon_scale':scale}
        try:
            row=matched_adjoint(gu,gd,u,v,lu=scale*np.array([1e-5,.003,.9]),ld=scale*np.array([2e-5,4e-4,.02]))
            row['parameters']=parameters;cases.append(row)
        except (ValueError,ArithmeticError,np.linalg.LinAlgError) as e:
            failed.append({'parameters':parameters,'accepted_as_prediction':False,'reason':str(e)})
    save('adjoint_matching.json',{'attempted_count':36,'accepted_count':len(cases),'cases':cases,
        'failed_or_uncontrolled_cases':failed,
        'scope':'Declared illustrative spectra and mediator masses; only the two existing mixing anchors are fitted. The Hermitian adjoint background is an initialized favorable ansatz, not a derived vacuum.'})
    conjugates=[]
    for gu,gd in ((0.,.5),(0.,1.),(.1,.5),(.1,1.)):
        p=matched_adjoint(gu,gd,u,v);m=matched_adjoint(gu,gd,u,v,phase=-11*pi/30)
        conjugates.append({'gu':gu,'gd':gd,'positive_input':p['observables'],'negative_input':m['observables']})
    save('CP_transmission.json',{'adjoint_conjugate_cases':conjugates,
        'column_phase_identity':'(Y diag(exp(i theta_j)))(Y diag(exp(i theta_j)))^dagger=Y Y^dagger',
        'universal_mass_phase':'A flavor-universal complex mass changes column singular values and an overall sector phase, not the orthogonal frame mixing.'})
    depths=[r['observables']['depth'] for r in cases]
    save('summary.json',{'ordinary_mediator_mass_yukawa_invariants':78,'with_complex_adjoint':82,
        'triplet_scalar_counts':{'degree2':6,'degree4':36,'degree6':166},
        'first_available_nonlinear_orthogonal_frame_orientation_degree':8,
        'conditional_orthogonal_frame_cases':len(transfers),
        'maximum_conditional_depth_error':max(abs(x['observables']['depth']-golden) for x in transfers),
        'adjoint_cases_attempted':36,'adjoint_cases_accepted':len(cases),'adjoint_failed_cases':len(failed),
        'adjoint_effective_depth_range':[min(depths),max(depths)],
        'all_accepted_adjoint_cases_fail_golden_at_one_percent':all(abs(x/golden-1)>.01 for x in depths),
        'status':'Shared mediators transmit an initialized orthogonal frame exactly after canonical normalization. The scoped low-degree alignment obstruction is exact; the initialized adjoint alternative fails golden enforcement. No complete predictive flavor theory has been derived.',
        'limitations':['Scalar orientation theorem assumes fixed positive norms and exact separate frame orthogonality.',
                       'No derived adjoint potential, anomaly-free gauged family symmetry, loop threshold matching or combined softly broken SUSY completion.',
                       'Degree-eight CP capability example gives democratic mixing rather than the hierarchical golden CKM target.'],
        'new_Lean_theorems':0,'new_experimental_data':False})
    save('sources.json',{'primary_sources':[
        {'url':'https://arxiv.org/abs/0910.5127','title':'Quark mixing sum rules and the right unitarity triangle','use':'Texture-zero route comparison; not a derivation of the nominated golden relation.'},
        {'url':'https://arxiv.org/abs/1103.2915','title':'On The Potential of Minimal Flavour Violation','use':'Comparison for limitations of low-degree dynamical flavor potentials. The six-triplet orthogonal-frame theorem here has its own stated assumptions and certificate.'},
        {'url':'https://arxiv.org/abs/1410.2057','title':'An SU(5) x A5 Golden Ratio Flavour Model','use':'Example of an explicit flavor/messenger construction. Its golden mixing result is in the neutrino sector, not the present CKM target.'}],
        'access':'Primary abstracts and metadata read; no claim of reproducing the full cited UV models.'})
    manifest={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.glob('*.json')) if p.name not in ('manifest.json','validation.json')}
    save('manifest.json',manifest)
    print(json.dumps({'receipts':len(manifest),'adjoint_accepted':len(cases),'adjoint_failed':len(failed),
                      'depth_range':[min(depths),max(depths)]}))


if __name__=='__main__':main()
