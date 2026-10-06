"""Reproduce the electroweak branch, scalar threshold and inverse spectra."""
from pathlib import Path
import json
import numpy as np
import mpmath as mp
from valentiner_electroweak import *
from develop_valentiner_canonical import fields,decoupling
from develop_valentiner_adjoint_uv import cp_transform
from valentiner_adjoint_quartics import quartic_projectors
from valentiner_higher_operators import census,quality_bound
from perfectpower.flavor_quantum import scalar_threshold,fermion_coleman_weinberg,fermion_CW_gradient
from perfectpower.flavor_canonical import current_pair
from perfectpower.flavor_kinetic import KineticCovariants,fixed_spectrum_bare_metric,matrix

ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'


def high_precision_threshold(D,result):
    # Independent 60-digit trace evaluation of the saved double eigenbasis.
    with mp.workdps(60):
        masses=[mp.mpf(str(v)) for v in result['fermion_masses']]
        total=mp.mpf(0)
        for a,s2 in enumerate(result['scalar_masses_squared']):
            G=matrix(result['mass_basis_vertices'][a]);y=mp.mpf(str(s2))
            for i,mi in enumerate(masses):
                for k,mk in enumerate(masses):
                    x=mk*mk
                    b=-mp.log(y) if x==y else 1-(x*mp.log(x)-y*mp.log(y))/(x-y)
                    total-=mp.im(G[i,k]*mk*G[k,i])*b/mi/(16*mp.pi**2)
        return mp.nstr(total,45)


def standard_CKM(s12=.22517,s13=.003763,s23=.04189,delta=1.154):
    c12,c13,c23=np.sqrt(1-np.array([s12,s13,s23])**2);e=np.exp(1j*delta)
    return np.array([[c12*c13,s12*c13,s13/e],
      [-s12*c23-c12*s23*s13*e,c12*c23-s12*s23*s13*e,s23*c13],
      [s12*s23-c12*c23*s13*e,-c12*s23-s12*c23*s13*e,c23*c13]])


def inverse_spectrum(f):
    # Yukawa eigenvalues are declared illustrative hierarchy inputs. CKM
    # central parameters are PDG 2026 equation 12.28, not a model prediction.
    V=standard_CKM();targets=[np.array([1e-5,.003,.9]),np.array([2e-5,.0004,.02])]
    frame=KineticCovariants(f[1].conj().T,f[2].conj().T@f[0].conj().T)
    rows=[];kernels=[]
    for sector,target,U,y in zip(['up','down'],targets,[np.eye(3),V],[1.2,.57]):
        k=match(*f,sector);N=np.linalg.solve(k['M'],k['C']);H=U@np.diag(target**2)@U.conj().T
        fitted=fixed_spectrum_bare_metric(y*np.eye(3),N,H)
        completion=frame.positive_completion(fitted['bare_metric'])
        kernels.append(dict(k,Y=fitted['matched_Y']))
        rows.append({'sector':sector,'target_Yukawa_eigenvalues':target.tolist(),'bare_Higgs_coefficient':y,
                     'minimum_bare_metric_eigenvalue':fitted['minimum_bare_metric_eigenvalue'],
                     'target_H_error_90_digits':fitted['target_H_error'],'positive_completion_error_90_digits':completion['error'],
                     'real_metric_coefficients':completion['real_coefficients']})
    result=decoupling(kernels)
    error=float(np.max(abs(np.array(result['abs_CKM'])-abs(V))))
    return {'sectors':rows,'matched_observables':result,'CKM_magnitude_error':error,
            'CKM_reference':'PDG 2026 review, equation 12.28, central inputs',
            'scope':'Constructive decoupling EFT matching with fitted real kinetic coefficients and illustrative hierarchical Yukawas. These field-dependent metrics are a distinct action from the canonical-bare one-loop benchmark.'}


def main():
    seed=np.array(json.loads((OUT/'valentiner_adjoint_uv.json').read_text())['vacuum']['field_coordinates'])
    projectors,_=quartic_projectors();records=[];reference=None
    for epsilon in [1.,.1,.01,.001,1e-5]:
        w,H,stationarity=branch(seed,projectors,vev=.03*epsilon);f=fields(w)
        kernels=[scaled_kernel(f,s,epsilon) for s in ['up','down']]
        spectra=[full_spectrum(k,.03*epsilon) for k in kernels];current=current_pair(*spectra)
        loops=[scalar_threshold(s['mass_matrix'],vertices(sector,epsilon),H) for sector,s in zip(['up','down'],spectra)]
        record={'spurion':epsilon,'joint_vacuum':stationarity,'weak_CP_quartet':current['CP_quartet'],
                'scalar_threshold_by_sector':[{'delta_theta':r['delta_theta'],'UV_phase_coefficient':r['UV_phase_coefficient'],
                        'relative_correction_norm':r['relative_correction_norm']} for r in loops],
                'combined_scalar_delta_theta':sum(r['delta_theta'] for r in loops)}
        records.append(record)
        if epsilon==1e-5:reference=(w,H,f,kernels,spectra,loops)
    w,H,f,kernels,spectra,loops=reference
    partner_w,partner_H,partner_stationarity=branch(cp_transform(w),projectors,vev=3e-7)
    partner_kernels=[scaled_kernel(fields(partner_w),s,1e-5) for s in ['up','down']]
    partner_spectra=[full_spectrum(k,3e-7) for k in partner_kernels]
    partner_loop=[scalar_threshold(s['mass_matrix'],vertices(sector,1e-5),partner_H) for sector,s in zip(['up','down'],partner_spectra)]
    cp_error=abs(sum(r['delta_theta'] for r in loops)+sum(r['delta_theta'] for r in partner_loop))
    fixed=fields(seed);base=[scaled_kernel(fixed,s) for s in ['up','down']]
    base_current=current_pair(*[full_spectrum(k,.03) for k in base])
    scaled=[scaled_kernel(fixed,s,1e-5) for s in ['up','down']]
    scaled_current=current_pair(*[full_spectrum(k,3e-7) for k in scaled])
    scale_error=float(np.max(abs(abs(base_current['V'])-abs(scaled_current['V']))))
    cwbase=sum(fermion_coleman_weinberg(full_spectrum(k,.03)['mass_matrix']) for k in base)
    cwsmall=sum(fermion_coleman_weinberg(full_spectrum(k,3e-7)['mass_matrix'],mu=1e-5) for k in scaled)
    cwgradient=sum((fermion_CW_gradient(s['mass_matrix'],vertices(sector,1e-5),mu=1e-5) for sector,s in zip(['up','down'],spectra)),np.zeros(71))
    # Match the Higgs soft mass to hold the chosen VEV. This single allowed
    # counterterm removes only its tadpole; no flavor tadpoles are subtracted.
    flavor_shift=np.linalg.solve(H[:70,:70],-cwgradient[:70])/COORDINATE_SCALES
    higgs_soft_shift=cwgradient[70]/(np.sqrt(2)*3e-7)
    operators=census()
    quality=[quality_bound(f,[match(*f,s) for s in ['up','down']],operators,cutoff,1e-5) for cutoff in [1e9,1e10,1e11,1e12,1e13]]
    result={'schema':'pp-valentiner-quantum/1','input_vacuum_receipt':'valentiner_adjoint_uv.json',
       'joint_branch_scan':records,'selected_field_coordinates':w.tolist(),
       'selected_CP_partner':{'joint_vacuum':partner_stationarity,'weak_CP_quartet':current_pair(*partner_spectra)['CP_quartet'],
                             'combined_scalar_delta_theta':sum(r['delta_theta'] for r in partner_loop),'opposite_phase_absolute_error':cp_error},
       'scalar_threshold_60_digit_trace_checks':[high_precision_threshold(s['mass_matrix'],r) for s,r in zip(spectra,loops)],
       'spurion_selection':{'new_Z6_charges':{'heavy_left':1,'heavy_right':0,'bare_quarks':2,'scalars_and_Higgs':0,'epsilon':1},
                           'heavy_mass_power':'epsilon','bare_heavy_source_power':'conjugate(epsilon)','Higgs_to_heavy_power':'epsilon^2',
                           'fixed_background_full_current_scale_residual':scale_error,
                           'scope':'Real positive spurion benchmark; technically small breaking parameter is an input. Weak currents stay fixed when Higgs and all fermion masses scale together.'},
       'fermion_vacuum_backreaction':{'CW_scale_ratio':cwsmall/cwbase,'expected_ratio':1e-20,
                                   'maximum_linearized_flavor_coordinate_shift':float(max(abs(flavor_shift))),
                                   'Higgs_soft_mass_matching_shift':float(higgs_soft_shift),
                                   'scope':'Fermionic Coleman-Weinberg contribution and linearized flavor response after Higgs tadpole matching; scalar-loop feedback is not included.'},
       'higher_fermion_operator_census':operators,'finite_EFT_quality_bounds':quality,
       'hierarchical_inverse_matching':inverse_spectrum(fixed),
       'loop_scope':'Finite zero-external-momentum neutral-real-scalar mass threshold, canonical bare fermion metrics, all 71 physical neutral scalar modes. This is not an all-loop strong-CP theorem. No inferred loop claim for the separately fitted kinetic action.',
       'references':{'neutral_scalar_matching':'https://arxiv.org/html/2407.16202v2#A1','CKM_benchmark':'https://pdg.lbl.gov/2026/reviews/rpp2026-rev-ckm-matrix.pdf'}}
    assert records[-1]['joint_vacuum']['minimum_71_scalar_mass_squared']>0
    print('threshold diagnostic',records[-1]['combined_scalar_delta_theta'],cp_error,flush=True)
    assert abs(records[-1]['combined_scalar_delta_theta'])<1e-10 and cp_error<5e-15
    assert result['hierarchical_inverse_matching']['CKM_magnitude_error']<1e-10
    text=json.dumps(result,indent=2,sort_keys=True)+'\n';(OUT/'valentiner_quantum.json').write_text(text)
    print(json.dumps({'selected_scalar_delta_theta':records[-1]['combined_scalar_delta_theta'],'CP_partner_error':cp_error,
                      'quality':quality[-2],'inverse_CKM_error':result['hierarchical_inverse_matching']['CKM_magnitude_error'],
                      'vacuum_backreaction':result['fermion_vacuum_backreaction']},indent=2))


if __name__=='__main__':main()
