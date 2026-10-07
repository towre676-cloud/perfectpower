"""Analytic logarithmic quartic geometry and the coupled 48-coordinate profile."""
import json
from pathlib import Path
import numpy as np
from perfectpower.logarithmic_quartic import *
from perfectpower.flavor_scalar_feedback import SingletScalarModel
from perfectpower.flavor_gauge_feedback import calibrated_vector_CW
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'

def build():
    b=json.loads((OUT/'flavor_singlet_mediation.json').read_text())['singlet_finite_UV'];model=SingletScalarModel(b)
    normal,coefficients=compile_vector_radial(model,model.vac)
    old=json.loads((OUT/'flavor_gauge_feedback.json').read_text())['tadpole_calibrated_hard_branches'][0];X=np.array(old['rescaled_coordinates_Y']);r=old['r']
    base=model.full_hessian(X)+r*model.loop_hessian(X);base=(base+base.T)/2
    delta=calibrated_vector_CW(X[20],model.vac[20],r)[2];H=base.copy();H[20,20]+=delta
    S,response=profile_hessian(H);S0,_=profile_hessian(base)
    indices=[j for j in range(len(X)) if j!=20];bvec=base[indices,20];c=base[20,20]
    rank=np.outer(bvec,bvec)*delta/(c*(c+delta));trans=np.eye(len(X));trans[20,indices]=-bvec/H[20,20]
    diagonal=trans.T@H@trans
    profile=profiled_hard_branch(model)
    return {'exact_identities':exact_radial_identities(),'universal_phase_census':[
        {'input':eta,'classification':LogQuartic(1.,1.,eta).classify()} for eta in [-1.,'fold',-.34,'coexistence',-.1,'origin',.1]],
        'control_response_at_coexistence':LogQuartic(1.,1.,'coexistence').control_response(),
        'compiled_benchmark_radial_slice':{'coefficients':coefficients,'classification':normal.classify()},
        'full_hard_background_profile':{'minimum_profiled_curvature':float(np.linalg.eigvalsh(S)[0]),'maximum_congruence_off_diagonal_error':float(np.max(abs(diagonal[20,indices]))),
            'maximum_profiled_block_congruence_error':float(np.max(abs(diagonal[np.ix_(indices,indices)]-S))),
            'radial_response_norm':float(np.linalg.norm(response)),
            'radial_response_norm_without_vector_stiffening':float(np.linalg.norm(profile_hessian(base)[1])),
            'rank_one_stiffening_identity_error':float(np.max(abs(S-S0-rank))),
            'rank_one_profiled_stiffening_eigenvalues':np.linalg.eigvalsh(rank).tolist()},
        'profiled_hard_branch':profile,'maximum_profiled_vs_full_solver_coordinate_difference':float(np.max(abs(np.array(profile['rescaled_coordinates_Y'])-X))),
        'references':['https://dlmf.nist.gov/4.13','https://arxiv.org/abs/hep-ph/0111209'],
        'scope':'Complete global radial classification and exact local elimination identities for a logarithmic quartic. Coupled numerical results are local to the declared calibrated hard potential; no gauge-independent global flavor vacuum or predicted CKM angle.'}

if __name__=='__main__':
    p=OUT/'flavor_radial_profile.json';p.write_text(json.dumps(build(),indent=2,sort_keys=True)+'\n');print(p)
