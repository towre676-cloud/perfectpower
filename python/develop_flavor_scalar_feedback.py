"""Full 49-field scalar/fermion force and exact weak continuation."""
from pathlib import Path
import json
import numpy as np
from perfectpower.flavor_scalar_feedback import *
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'

def calculate(model,mu):
    H=model.full_hessian(model.vac);derivatives=model.vacuum_derivatives();sg=scalar_CW_gradient(H,derivatives,mu);spectra,G=model.fermions();fg=sum((fermion_CW_gradient(s['mass_matrix'],v,mu) for s,v in zip(spectra,G)),np.zeros(len(H)))
    g=sg+fg;shift=-np.linalg.solve(H,g);_,D=model.current(model.z);sourceH=H[:21,:21]-D.T@D/model.M**2;profile=sg[:21]-D.T@sg[21:]/model.M**2;T=model.angular_tangents();AH=T.T@sourceH@T;angular=-np.linalg.solve(AH,T.T@profile)
    checks=[]
    for j in [0,5,8,11]:
        v=T[:,j];e=2e-5;energies=[]
        for sign in [-1,1]:
            z=model.z+sign*e*v;J,_=model.current(z);energies.append(scalar_CW(model.full_hessian(np.r_[z,-J/model.M**2]),mu))
        numeric=(energies[1]-energies[0])/(2*e);exact=float(v@profile);checks.append({'column':j,'spectral_trace_derivative':exact,'direct_CW_difference':numeric,'absolute_error':abs(numeric-exact)})
    return {'MS_scale':mu,'scalar_CW':scalar_CW(H,mu),'scalar_gradient':sg.tolist(),'fermion_gradient':fg.tolist(),'full_linear_shift':shift.tolist(),'linear_shift_over_full_background':float(np.linalg.norm(shift)/np.linalg.norm(model.vac)),
            'source_shift_over_source_background':float(np.linalg.norm(shift[:21])/np.linalg.norm(model.z)),
            'minimum_full_Hessian_eigenvalue':float(np.linalg.eigvalsh(H)[0]),'minimum_isospectral_angular_Hessian_eigenvalue':float(np.linalg.eigvalsh(AH)[0]),
            'isospectral_angular_scalar_force_norm':float(np.linalg.norm(T.T@profile)),
            'isospectral_angular_fermion_force_norm':float(np.linalg.norm(T.T@(fg[:21]-D.T@fg[21:]/model.M**2))),
            'constrained_angular_linear_shift_over_source_norm':float(np.linalg.norm(angular)/np.linalg.norm(model.z)),
            'angular_finite_difference_checks':checks,'scope':'All 49 massive neutral scalars and twelve coloured Dirac states. Three massless Higgs Goldstones contribute zero to this first CW gradient by the x log x limit. Gauge loops omitted. Linear shifts are diagnostics, not solved quantum vacua.'}

def build():
    b=json.loads((OUT/'flavor_singlet_mediation.json').read_text())['singlet_finite_UV'];gaussian=SingletScalarModel(b,False);model=SingletScalarModel(b,True);full=calculate(model,1.);control=calculate(gaussian,1.);at_threshold=calculate(model,10.)
    H=model.full_hessian(model.vac);spectra,G=model.fermions();threshold=[scalar_threshold(s['mass_matrix'],v,H) for s,v in zip(spectra,G)];continuations=[]
    g=full['full_linear_shift']
    for r in [1.,.1,.01,.001,.0001,.000001]:
        scaled=model.full_hessian(np.sqrt(r)*(model.vac/np.sqrt(r)));errors=[]
        for f,(eta,t,A) in enumerate(nonet_fields(model.z[:20]/np.sqrt(r))):
            C=np.sqrt(r)*((.1*eta+.7*t)*np.eye(3)+.8*A);m=model.bare[f]+np.sqrt(r)*model.h[f]*(model.vac[-1]/np.sqrt(r));ss=block_spectrum(C,np.sqrt(r)*[1.2,.57][f],m,model.z[20]/np.sqrt(2*r));errors.append(float(np.max(abs(ss['mass_matrix']-spectra[f]['mass_matrix']))))
        packets=[scalar_threshold(s['mass_matrix'],np.sqrt(r)*v,scaled) for s,v in zip(spectra,G)]
        continuations.append({'r':r,'maximum_tree_fermion_matrix_error':max(errors),'maximum_scalar_Hessian_error':float(np.max(abs(scaled-H))),
            'predicted_relative_linear_shift':r*full['linear_shift_over_full_background'],
            'predicted_source_relative_linear_shift':r*full['source_shift_over_source_background'],
            'minimum_bare_Hessian_at_linear_displacement':float(np.linalg.eigvalsh(model.full_hessian(model.vac+r*np.array(g)))[0]),
            'neutral_scalar_relative_correction_norms':[p['relative_correction_norm'] for p in packets],
            'neutral_first_order_phases':[p['delta_theta'] for p in packets],
            'maximum_mass_correction_scaling_error':float(max(np.max(abs(p['mass_basis_correction']-r*q['mass_basis_correction'])) for p,q in zip(packets,threshold)))})
    return {'weak_continuation_theorem':weak_continuation_certificate(),'non_Gaussian_full_feedback':full,'Gaussian_control':control,'non_Gaussian_feedback_at_mediator_scale':at_threshold,
        'neutral_loop_stationary_branch':neutral_loop_stationary_branch(model),
        'same_tree_Hessian_maximum_error':float(np.max(abs(H-gaussian.full_hessian(gaussian.vac)))),'angular_force_extension_difference':full['isospectral_angular_scalar_force_norm']-control['isospectral_angular_scalar_force_norm'],
        'continuations':continuations,'scope':'Conditional local weak-coupling family with unchanged tree spectra and physical mixing. Relative linear shift is perturbative evidence only; no global/quantum stationary vacuum or observed gauge-coupling fit.'}

if __name__=='__main__':
    path=OUT/'flavor_scalar_feedback.json';path.write_text(json.dumps(build(),indent=2,sort_keys=True)+'\n');print(path)
