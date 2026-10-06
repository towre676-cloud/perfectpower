"""Exact angle carrier and fixed-spectrum electromagnetic/weak-phase orbit."""
from pathlib import Path
import json
import numpy as np
import sympy as sy
from perfectpower.flavor_hermitian import (source_for_light_masses,block_spectrum,
    doublet_weights,polynomial_calibration,nonet_target)
from perfectpower.flavor_canonical import current_pair
from perfectpower.flavor_completion import physical_chart
from perfectpower.flavor_prediction import cyclotomic_golden_carrier
from perfectpower.flavor_electromagnetic import photon_screening,logarithmic_threshold,determinant_log_threshold
from develop_valentiner_quantum import standard_CKM
from develop_valentiner_canonical import fields

ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'


def angle_certificate():
    z,x=sy.symbols('z x');phi=sy.Poly(sy.cyclotomic_poly(60,z),z);P=x**8-7*x**6+14*x**4-8*x**2+1
    assert sy.expand(z**8*P.subs(x,z+1/z)-phi.as_expr())==0
    C=sy.rem(1-z**12-z**48,phi.as_expr(),z)
    assert sy.rem(C*C-3*C+1,phi.as_expr(),z)==0
    small=[k for k in range(1,30) if sy.gcd(k,60)==1 and k%5 in (1,4)]
    return {'primitive_order':60,'selected_embedding_index':11,'theta_radians':'11*pi/30',
        'theta_degrees':66,'real_angle_minimal_polynomial':str(P),
        'golden_identity':'C=1-2cos(12 theta)=(3-sqrt(5))/2; C^2-3C+1=0',
        'positive_half_circle_small_C_angles':[6*k for k in small],
        'CP_partner_angle_degrees':-66,'golden_carrier':cyclotomic_golden_carrier(),
        'selection_scope':'This exact algebraic carrier does not select its embedding or impose a physical CKM angle.'}


def develop():
    saved=json.loads((OUT/'valentiner_hermitian.json').read_text());L,A,_,_=fields(np.array(saved['base_field_coordinates']))
    R=A@A.conj().T/saved['polynomial_normalizations']['R_scale'];T=L@L.conj().T/saved['polynomial_normalizations']['T_scale']
    y=[1.2,.57];m=[1.,1.];v=.03;ell=[v*np.array([1e-5,.003,.9]),v*np.array([2e-5,.0004,.02])]
    h=[source_for_light_masses(a,b,c,v) for a,b,c in zip(ell,y,m)]
    up=block_spectrum(np.diag(h[0]),y[0],m[0],v);qu,qd=[doublet_weights(a,b,c,v) for a,b,c in zip(ell,y,m)]
    points=[0,6,42,60,66,78,90,114,138,174,180,-66];momenta=[1e-5,.01,1.,100.];rows=[]
    for angle in points:
        U=standard_CKM(delta=np.deg2rad(angle));C=U@np.diag(h[1])@U.conj().T
        down=block_spectrum(C,y[1],m[1],v);curr=current_pair(up,down)
        # Recover the source frame's unitary chart from the exact finite weights.
        V=curr['V']/qu[:,None]/qd[None,:];chart=physical_chart(V)
        calibration=polynomial_calibration(R,T,nonet_target(C))
        screening=[photon_screening(Q,up['masses'],2/3)+photon_screening(Q,down['masses'],-1/3) for Q in momenta]
        threshold=logarithmic_threshold(up['masses'],2/3)+logarithmic_threshold(down['masses'],-1/3)
        em_error=max(np.max(abs(S['left'].conj().T@np.eye(6)@S['left']-np.eye(6))) for S in [up,down])
        rows.append({'initialized_source_frame_phase_degrees':angle,'recovered_unitary_chart':chart,
            'finite_CP_quartet':curr['CP_quartet'],'six_down_masses':down['masses'].tolist(),
            'photon_screening_at_spacelike_momenta':screening,'all_state_logarithmic_threshold':threshold,
            'electromagnetic_generator_identity_error':float(em_error),
            'real_polynomial_source_coefficients':calibration['coefficients'],
            'source_center_reconstruction_error':calibration['target_error']})
    spectra=np.array([a['six_down_masses'] for a in rows]);screen=np.array([a['photon_screening_at_spacelike_momenta'] for a in rows])
    reference=determinant_log_threshold(y[0],v,m[0],2/3)+determinant_log_threshold(y[1],v,m[1],-1/3)
    result={'schema':'pp-flavor-electromagnetic/1','angle_exact_certificate':angle_certificate(),
        'measured_reference':{'CODATA_adjustment':2022,'alpha_zero_momentum':'0.0072973525643','alpha_inverse_zero_momentum':'137.035999177',
            'alpha_inverse_standard_uncertainty':'0.000000021','role':'External measured reference, never used to calibrate the orbit.',
            'source':'https://physics.nist.gov/cuu/Constants/Table/allascii.txt'},
        'gauge_boundary_operator':{'operator':'-k0 F_mu_nu F^mu_nu/4','normalization':'unit-charge covariant derivative; k0=1/e^2, alpha^-1=4*pi*k0',
            'allowed_by':'All stated flavor, shaping and CP symmetries','independent_coefficient':True},
        'one_loop_photon_theorem':'Equal electric charge on each complete sector implies Q_L=Q_R=Q_f I_6 in every mass basis; one-loop photon polarization is spectral and independent of mixing frames.',
        'one_loop_all_state_log_identity':'sum_i log(mu/m_i)=6log(mu)-3log(v*y*m) independently of C',
        'spacelike_momenta_model_units':momenta,'phase_orbit':rows,
        'maximum_mass_relative_change':float(np.max(abs(spectra/spectra[0]-1))),
        'maximum_screening_change':float(np.max(abs(screen-screen[0]))),
        'maximum_threshold_identity_error':max(abs(a['all_state_logarithmic_threshold']-reference) for a in rows),
        'scope':'Perturbative one-loop fermion photon contribution on a specified canonical model and source-center orbit. No hadronic alpha(0) conversion, electroweak multi-loop matching or predictive UV gauge boundary is provided. Weak phases in the orbit are initialized counterexamples, not symmetry-selected predictions.',
        'primary_reference':'https://pdg.lbl.gov/2026/reviews/rpp2026-rev-standard-model.pdf'}
    assert result['maximum_mass_relative_change']<1e-9 and result['maximum_screening_change']<1e-9
    (OUT/'flavor_electromagnetic.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ['maximum_mass_relative_change','maximum_screening_change','maximum_threshold_identity_error']},indent=2))
    return result


if __name__=='__main__':develop()
