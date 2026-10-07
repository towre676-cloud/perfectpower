"""Fixed electroweak gauge inputs, finite Higgs calibration and Goldstone Ward test."""
import json
from pathlib import Path
import numpy as np
from perfectpower.flavor_scalar_feedback import SingletScalarModel
from perfectpower.flavor_gauge_feedback import *
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions'

def build():
    b=json.loads((OUT/'flavor_singlet_mediation.json').read_text())['singlet_finite_UV'];model=SingletScalarModel(b)
    T=model.angular_tangents();_,D=model.invariants(model.z)
    branches=[calibrated_hard_branch(model,r=r) for r in [1e-6,3e-7,1e-7]]
    return {'exact_identities':exact_gauge_identities(),
        'inputs':{'g':.65,'gprime':.36,'MS_scale':1.,'couplings_are_declared_inputs_not_a_SM_fit':True,'only_electroweak_charged_scalar':'One canonical Higgs doublet; all source and mediator fields are gauge singlets.'},
        'raw_fixed_gauge_continuation':[raw_fixed_gauge_diagnostic(model,r=r) for r in [1.,.1,.001,1e-6]],
        'maximum_quadratic_portal_isospectral_derivative':float(np.max(abs(D[:8]@T))),
        'tadpole_calibrated_hard_branches':branches,
        'Goldstone_organization':{'prescription':'Landau-MS one-loop anti-resummation: massless Goldstone propagators with squared masses treated as loop-order insertions; one-loop pure Goldstone vacuum integrals vanish in dimensional regularization.',
            'implemented':'Zero pure-Goldstone one-loop potential and Ward tadpole diagnostic.',
            'not_implemented':'Two-loop insertion diagrams, momentum-dependent Goldstone self-energy, electroweak pole/current matching and RG improvement.',
            'references':['https://arxiv.org/abs/hep-ph/0111209','https://arxiv.org/abs/1406.2355','https://arxiv.org/abs/2608.04182']},
        'scope':'The finite Higgs mass adjustment is a calibration input. Stable hard-potential branches retain physical CP conditionally; gauge radial dominance precludes claiming a uniformly small loop expansion. Neither fixed physical Higgs/W/Z masses, a gauge-independent quantum vacuum nor golden flavor is predicted.'}

if __name__=='__main__':
    p=OUT/'flavor_gauge_feedback.json';p.write_text(json.dumps(build(),indent=2,sort_keys=True)+'\n');print(p)
