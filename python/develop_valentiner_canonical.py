"""Reproduce canonical currents, the determinant audit and the NB completion."""
from pathlib import Path
import json
import numpy as np
import mpmath as mp
from perfectpower.flavor_canonical import *
from perfectpower.flavor_kinetic import matrix,array
from perfectpower.flavor_completion import physical_chart
from valentiner_adjoint_uv import uv_unpack,unpack,RHO,EPSILON,MEDIATOR_MASS,BASIS
from valentiner_adjoint_quarks import match as old_match
from valentiner_canonical_quarks import match as nb_match,PARAMETERS
from develop_valentiner_adjoint_uv import cp_transform
from valentiner_canonical_operators import certificate as operator_certificate
from perfectpower.flavor_kinetic import KineticCovariants,fixed_spectrum_bare_metric,hermitian_function
from itertools import combinations

ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'


def fields(w):
    x,t=uv_unpack(np.asarray(w));L,A,B=unpack(x)
    S=np.sqrt(EPSILON)*RHO**5/MEDIATOR_MASS*np.einsum('a,aij->ij',t,BASIS)
    return RHO*L,RHO*A,RHO*B,S


def old_kernel(f,sector):
    r=old_match(*f,sector);k=canonical_kernel(r['heavy_row'],r['higgs_row'])
    k.update({key:r[key] for key in ['M','C','unnormalized_Y']});return k


def decoupling(kernels):
    U,us,_=np.linalg.svd(kernels[0]['Y']);D,ds,_=np.linalg.svd(kernels[1]['Y'])
    V=dagger(U[:,::-1])@D[:,::-1]
    record=physical_chart(V);record.update({'spectra':[us[::-1].tolist(),ds[::-1].tolist()],'abs_CKM':abs(V).tolist()})
    return record


def multiprecision_record(kernels,vev):
    with mp.workdps(80):
        frames=[];masses=[];phase=mp.mpc(1)
        for k in kernels:
            D=matrix(np.vstack([vev*k['T'],k['F']]));H=D*D.H
            ev,U=mp.eighe(H);frames.append(U[:3,:3]);masses.append([mp.nstr(mp.sqrt(v),65) for v in list(ev)[:3]])
            phase*=mp.det(D)/abs(mp.det(D))
        V=frames[0].H*frames[1]
        J=mp.im(V[0,1]*V[1,2]*mp.conj(V[0,2])*mp.conj(V[1,1]))
        return {'precision_digits':80,'light_masses':masses,'CP_quartet':mp.nstr(J,65),
                'full_determinant_phase':mp.nstr(mp.arg(phase),65),'abs_current':abs(array(V)).tolist()}


def exact_decimal_NB_determinant(f):
    """Reconstruct real coefficients before products, avoiding float asymmetry."""
    with mp.workdps(80):
        L,A,B,S=[matrix(v) for v in f];phases=[];errors=[]
        for sector in ['up','down']:
            d,a,b,lf,lr,sf,sr,cl,ca,y=[mp.mpf(str(v)) for v in PARAMETERS[sector]]
            M=mp.zeros(9)
            for start,v in [(0,d),(3,a),(6,b)]:
                for i in range(3):M[start+i,start+i]=v
            for row,col,block in [(0,6,lf*B),(6,0,lr*B.H),(3,6,sf*S),(6,3,sr*S.H)]:
                for i in range(3):
                    for j in range(3):M[row+i,col+j]=block[i,j]
            det=mp.det(M);phases.append(mp.nstr(mp.arg(det),65));errors.append(mp.nstr(abs(mp.im(det)),65))
        return {'precision_digits':80,'heavy_determinant_phases':phases,'heavy_determinant_imaginary_errors':errors,
                'coefficient_construction':'Exact decimal real benchmark coefficients multiply the converted vacuum fields before determinant evaluation.'}


def finite_record(kernels,vev):
    spectra=[full_spectrum(k,vev) for k in kernels];current=current_pair(*spectra)
    approximations=[dimension_six(k,vev) for k in kernels];approx=current_pair(*approximations)
    Nu,Nd=[s['doublet_frame'] for s in spectra]
    full=dagger(spectra[0]['left'][:3])@spectra[1]['left'][:3]
    ncu=dagger(spectra[0]['left'][:3])@spectra[0]['left'][:3]
    ncd=dagger(spectra[1]['left'][:3])@spectra[1]['left'][:3]
    row_res=max(abs((current['row_deficit']-sum(current['row_positive_parts'])).ravel()))
    col_res=max(abs((current['column_deficit']-sum(current['column_positive_parts'])).ravel()))
    masses=[s['masses'].tolist() for s in spectra]
    higgs_errors=[]
    for k,s in zip(kernels,spectra):
        h=higgs_coupling(s,k['T']);nc=dagger(s['left'][:3])@s['left'][:3]
        higgs_errors.append(float(np.max(abs(h-nc*s['masses'][None,:]/vev))))
    determinant_error=[]
    for k,s in zip(kernels,spectra):
        phase=determinant_phase(k['M'],k['unnormalized_Y'])
        sign,logabs=np.linalg.slogdet(s['mass_matrix'])
        determinant_error.append({'phase_error':float(abs(sign-phase['phase_factor'])),
                                  'log_magnitude_error':float(abs(logabs-3*np.log(vev)-phase['log_abs_coefficient']))})
    return {'vev':vev,'all_masses':masses,'abs_light_current':abs(current['V']).tolist(),
            'CP_quartet':current['CP_quartet'],'all_nine_CP_quartets':current['quartets'],
            'row_deficit_eigenvalues':np.linalg.eigvalsh(current['row_deficit']).tolist(),
            'column_deficit_eigenvalues':np.linalg.eigvalsh(current['column_deficit']).tolist(),
            'neutral_current_offdiagonal_max':[float(np.max(abs(s['neutral_current']-np.diag(np.diag(s['neutral_current']))))) for s in spectra],
            'neutral_current_loss_eigenvalues':[np.linalg.eigvalsh(np.eye(3)-s['neutral_current']).tolist() for s in spectra],
            'positive_decomposition_residual':float(max(row_res,col_res)),
            'full_current_partial_isometry_residual':float(max(np.max(abs(full@dagger(full)-ncu)),np.max(abs(dagger(full)@full-ncd)))),
            'determinant_identity_errors':determinant_error,
            'full_Higgs_neutral_current_identity_errors':higgs_errors,
            'pole_certificates':[pole_certificate(k,s,vev) for k,s in zip(kernels,spectra)],
            'dimension_six_current_magnitude_error':float(np.max(abs(abs(current['V'])-abs(approx['V'])))),
            'dimension_six_light_mass_relative_error':float(max(np.max(abs(a['masses']/s['masses'][:3]-1)) for a,s in zip(approximations,spectra)))}


def legacy_determinant_certificate(f,kernels):
    L,A,B,S=f;I=np.eye(3)
    up=np.block([[A,.71*L],[(-.4/2.)*B@S.conj().T,1.3*I-(.4*.2/2.)*B@B.conj().T]])
    down=np.block([[(-.4/2.)*A@S,.71*L],[B,1.3*I]])
    factors=[-h**3*2.**3*np.linalg.det(q) for h,q in zip([.6,.57],[up,down])]
    direct=[np.linalg.det(k['M'])*np.linalg.det(k['unnormalized_Y']) for k in kernels]
    assert max(abs(a/b-1) for a,b in zip(factors,direct))<1e-9
    return {'reduced_six_by_six_relative_errors':[float(abs(a/b-1)) for a,b in zip(factors,direct)],
            'combined_strong_phase_at_theta_QCD_zero':float(np.angle(factors[0]*factors[1])),
            'independent_of_Higgs_scale':True,'positive_canonical_metrics_cannot_change_phase':True,
            'scope':'Tree-level theta_QCD=0 in the real-coupling basis. An anomalous chiral rephasing transfers the phase to theta rather than removing it.'}


def NB_kinetic_test(f,kernels):
    L,A,B,S=f;up,down=kernels;Y0=down['unnormalized_Y'];null=np.linalg.solve(down['M'],down['C'])
    frame=KineticCovariants(A.conj().T,B.conj().T@L.conj().T)
    U=np.linalg.svd(up['Y'])[0][:,::-1];rows=[];responses=[]
    with mp.workdps(90):
        u=matrix(U);u=u*hermitian_function(u.H*u,lambda v:1/mp.sqrt(v));d=matrix(down['Y']);Hd=d*d.H
        for i,j in combinations(range(3),2):
            for kind in ['real','imaginary']:
                g=mp.zeros(3)
                if kind=='real':g[i,j]=1;g[j,i]=-1
                else:g[i,j]=g[j,i]=mp.j
                pair=[]
                for sign in [-1,1]:
                    angle=mp.mpf(str(sign*1e-5));rot=u*mp.expm(angle*g)*u.H;target=rot*Hd*rot.H
                    m=fixed_spectrum_bare_metric(Y0,null,target);completion=frame.positive_completion(m['bare_metric'])
                    changed=dict(down,Y=m['matched_Y']);r=decoupling([up,changed]);pair.append(r)
                    rows.append({'plane':[i,j],'kind':kind,'angle':float(angle),'minimum_bare_metric_eigenvalue':m['minimum_bare_metric_eigenvalue'],
                                 'positive_polynomial_completion_error':completion['error'],'target_H_error':m['target_H_error'],
                                 'observables':r,'strong_determinant_phase_preserved':True})
                responses.append([(pair[1][key]-pair[0][key])/2e-5 for key in ['Vus','Vcb','Vub','J']])
    response=np.array(responses).T;ref=decoupling(kernels);scaled=response/np.array([abs(ref[k]) for k in ['Vus','Vcb','Vub','J']])[:,None]
    sv=np.linalg.svd(scaled/np.linalg.norm(scaled,axis=0),compute_uv=False)
    mass_error=max(np.max(abs(np.log(np.array(r['observables']['spectra'])/np.array(ref['spectra'])))) for r in rows)
    assert sv[-1]>1e-4 and mass_error<1e-9
    return {'metrics':rows,'four_response_singular_values':sv.tolist(),'six_decoupling_mass_log_residual':float(mass_error),
            'scope':'Same scalar vacuum and renormalizable mass/Yukawa matrices; allowed higher kinetic covariants alter four mixing directions at fixed six decoupling masses. Their determinants are positive, hence tree strong CP remains zero.'}


def main():
    previous=json.loads((OUT/'valentiner_adjoint_uv.json').read_text());w=previous['vacuum']['field_coordinates'];f=fields(w)
    legacy=[old_kernel(f,s) for s in ['up','down']];nb=[nb_match(*f,s) for s in ['up','down']]
    scans=[finite_record(nb,v) for v in [.001,.003,.01,.03,.1,.3]]
    oldscans=[finite_record(legacy,v) for v in [.003,.03,.3]]
    massscans=[]
    for scale in [1.,.1,.01,.001,.0001]:
        k=[nb_match(*f,s,mass_scale=scale) for s in ['up','down']]
        massscans.append({'mass_scale':scale,'observables':decoupling(k)})
    partners=[nb_match(*fields(cp_transform(np.asarray(w))),s) for s in ['up','down']]
    cp=decoupling(partners);ref=decoupling(nb)
    vev=.03;check=multiprecision_record(nb,vev);oldcheck=multiprecision_record(legacy,vev)
    assert abs(float(check['CP_quartet'])-scans[3]['CP_quartet'])<1e-12
    assert abs(float(check['full_determinant_phase']))<1e-12
    assert abs(cp['J']+ref['J'])<1e-12
    residual=max(np.max(abs(np.array(r['observables']['abs_CKM'])-np.array(ref['abs_CKM']))) for r in massscans)
    assert residual<1e-9 and abs(ref['J'])>1e-7
    theta=legacy_determinant_certificate(f,legacy)
    L,A,B,S=f;y=PARAMETERS['down'][-1]
    # A real-coefficient allowed dimension-seven Yukawa operator.
    quality=[]
    for cutoff in [1.,10.,100.]:
        correction=np.linalg.det(L)/cutoff**3
        quality.append({'cutoff_in_messenger_units':cutoff,'real_coefficient':1.,
                        'strong_phase':float(3*np.angle(y+correction))})
    result={'schema':'pp-valentiner-canonical/1','input_vacuum_receipt':'valentiner_adjoint_uv.json',
            'scalar_vacuum_and_potential_unchanged':True,
            'old_assignment_determinant_audit':theta,'old_assignment_finite_scans':oldscans,'old_assignment_80_digit_check':oldcheck,
            'NB_assignment':{'Q_L_u_R_d_R':'(3_u;0,0)','heavy_D':'(3_d;0,0)','heavy_H_A':'(3_H;-1,0)','heavy_H_B':'(3_H;0,-1)',
                             'heavy_electroweak_representation':'color-triplet SU(2)-singlet, charge 2/3 or -1/3 by sector',
                             'renormalizable_real_coefficients_per_sector':10,'parameters':{k:list(v) for k,v in PARAMETERS.items()},
                             'Higgs_row':'[y I,0,0,0]','bare_mass_rows':'C=[lambda_L L-dagger;lambda_A A-dagger;0]',
                             'heavy_mass_matrix':'[[m_D I,0,b B],[0,m_A I,s S],[c B-dagger,t S-dagger,m_B I]]',
                             'kinetic_assumption':'Canonical renormalizable bare metrics. Positive Hermitian metric changes preserve the full determinant phase, while generally changing weak mixing.'},
            'NB_Hermitian_similarity':[{'sector':s,'residual':float(np.max(abs(k['hermitian_similarity']-dagger(k['hermitian_similarity'])))),
                                       'minimum_eigenvalue':float(np.linalg.eigvalsh(hermitian(k['hermitian_similarity']))[0]),
                                       'determinant_phase':float(np.angle(np.linalg.slogdet(k['M'])[0]))} for s,k in zip(['up','down'],nb)],
            'NB_exact_operator_certificate':operator_certificate(),'NB_fixed_mass_kinetic_test':NB_kinetic_test(f,nb),
            'NB_exact_decimal_determinants':exact_decimal_NB_determinant(f),
            'NB_decoupling_observables':ref,'NB_CP_partner_observables':cp,'NB_finite_scans':scans,'NB_80_digit_check':check,
            'common_messenger_scale_scan':massscans,'scale_scan_mixing_magnitude_residual':float(residual),
            'dimension_seven_quality_operator':{'operator':'det(L) bar(Q_L) H d_R / Lambda^3 + h.c.',
                                               'CP_even_real_coefficient_allowed':True,'det_L_real':float(np.linalg.det(L).real),'det_L_imaginary':float(np.linalg.det(L).imag),
                                               'strong_phase_scan':quality,'leading_phase':'3 c Im(det L)/(y_d Lambda^3)'},
            'literature':[{'title':'Consequences of vector-like quarks of Nelson-Barr type','url':'https://arxiv.org/abs/2004.11318'},
                          {'title':'Effective theory analysis for vector-like quark model','url':'https://arxiv.org/abs/1801.05268'}],
            'conclusion':'A changed fermion representation assignment makes the same shared-adjoint vacuum a renormalizable tree-level Nelson-Barr realization: six nonzero light masses, physical weak CP and vanishing strong phase. The universal Higgs contraction makes mixing frames exactly independent of a common messenger scale in each sector at decoupling. Finite-scale currents are nonunitary and correlated with neutral currents. Higher-degree Yukawa operators, quantum strong CP, observed mass/mixing fits and golden protection remain open.'}
    (OUT/'valentiner_canonical.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'NB':ref,'legacy_theta':theta,'MP_CP':check['CP_quartet'],'scale_frame_residual':residual,'quality':quality},indent=2))


if __name__=='__main__':main()
