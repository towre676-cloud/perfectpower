"""Complete minimal nonet potential, CP branch and fixed-spectrum response."""
from pathlib import Path
import json
import numpy as np
from scipy.optimize import minimize,root
from scipy.linalg import qr
from perfectpower.nonet_potential import *
from perfectpower.ckm_constraint_geometry import *
from perfectpower.flavor_hermitian import block_spectrum,paired_vertex_reality
from valentiner_adjoint_quartics import quartic_projectors,adjoint
from develop_valentiner_frames import generators,numeric

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions/valentiner_nonet_joint.json'


def frame_and_spectrum(z):
    frames=[];sectors=[]
    for f,(eta,s,A) in enumerate(nonet_fields(z[:20])):
        C=.1*eta*np.eye(3)+.7*s*np.eye(3)+.8*A
        spectrum=block_spectrum(C,[1.2,.57][f],1.,z[20]/np.sqrt(2))
        Q=spectrum['doublet_frame'];weights=np.linalg.norm(Q,axis=0)
        frames.append(Q/weights);sectors.append(spectrum)
    V=frames[0].conj().T@frames[1]
    return frame_constraints(V),sectors,V


def source_eigenvalues(x):
    return np.concatenate([np.linalg.eigvalsh(.1*eta*np.eye(3)+.7*s*np.eye(3)+.8*A) for eta,s,A in nonet_fields(x)])


def source_jacobian(x):
    E=np.zeros((6,20))
    for f,(eta,s,A) in enumerate(nonet_fields(x)):
        w,U=np.linalg.eigh(.1*eta*np.eye(3)+.7*s*np.eye(3)+.8*A)
        for i in range(3):
            E[3*f+i,10*f:10*f+2]=[.1,.7]
            E[3*f+i,10*f+2:10*f+10]=.8*np.einsum('i,kij,j->k',U[:,i].conj(),BASIS,U[:,i]).real
    return E


def hessian(fun,z,h=.01):
    H=np.column_stack([(fun(z+np.eye(len(z))[i]*h)[1]-fun(z-np.eye(len(z))[i]*h)[1])/(2*h) for i in range(len(z))])
    F=np.column_stack([(fun(z+np.eye(len(z))[i]*h/2)[1]-fun(z-np.eye(len(z))[i]*h/2)[1])/h for i in range(len(z))])
    H=(4*F-H)/3
    return (H+H.T)/2


def build():
    P,pcert=quartic_projectors();P=np.array(P);scan=[];selected=None
    # Stop at the first isolated, nondegenerate, weak-CP-breaking branch.
    # Neither a nominated angle nor an observed mixing magnitude is tested.
    for index in range(24):
        c,rng=search_coefficients(index)
        for start in range(4):
            result=minimize(lambda x:potential(x,c,P),rng.normal(size=20)*.4,jac=True,method='BFGS',options={'gtol':1e-8,'maxiter':1600})
            x=result.x;H=numerical_hessian(x,c,P)
            obs,_,_=frame_and_spectrum(np.r_[x,np.sqrt(2)*.03])
            gaps=min(np.min(np.diff(w)) for w in source_eigenvalues(x).reshape(2,3))
            row={'coefficient_seed':20261006+index,'start':start,'energy':float(result.fun),
                 'gradient_norm':float(np.linalg.norm(result.jac)),'hessian_min':float(np.linalg.eigvalsh(H)[0]),
                 'J':obs['J'],'minimum_source_eigenvalue_gap':float(gaps)}
            scan.append(row)
            if row['hessian_min']>1e-6 and abs(obs['J'])>1e-5 and gaps>1e-3:
                selected=(x,c,index,start);break
        if selected is not None:break
    if selected is None:raise RuntimeError('Declared scan did not produce the required branch')
    x,c,index,start=selected
    portals=np.arange(1,9)*1e-7;portals[[2,6]]*=.1;vev=.03;lam=.13
    shifted=c.copy();shifted[:8]+=vev**2*portals
    refined=root(lambda x:potential(x,shifted,P)[1],x,tol=1e-11);x=refined.x
    mu2=2*lam*vev**2+operators(x,P)[0][:8]@portals;z=np.r_[x,np.sqrt(2)*vev]
    fun=lambda z:joint_higgs(z,c,P,portals,mu2,lam)
    H=hessian(fun,z);evals,O=np.linalg.eigh(H)
    obs,sectors,V=frame_and_spectrum(z)
    values,grad=operators(x,P)
    DX=-np.linalg.solve(H,np.vstack([grad[32:].T,np.zeros((1,28))]))
    def response(directions):
        step=1e-7
        return np.column_stack([(np.array(frame_and_spectrum(z+step*dx)[0]['squared_magnitudes'])-
                                 np.array(frame_and_spectrum(z-step*dx)[0]['squared_magnitudes']))/(2*step) for dx in directions.T])
    R=response(DX)
    # Restore all six signed source eigenvalues by six independent allowed
    # quadratic coefficients; the finite masses and current weights are fixed.
    HQ=numerical_hessian(x,shifted,P);DQ=-np.linalg.solve(HQ,grad[:8].T);DG=-np.linalg.solve(HQ,grad[32:].T)
    E=source_jacobian(x);T=E@DQ;chosen=qr(T,pivoting=True)[2][:6]
    DCC=-np.linalg.solve(T[:,chosen],E@DG);FIX=DG+DQ[:,chosen]@DCC
    RF=response(np.vstack([FIX,np.zeros((1,28))]));columns=qr(RF,pivoting=True)[2][:4]
    baseline_eigen=source_eigenvalues(x);finite=[];epsilon=2e-7
    for col in columns:
        sides=[]
        for sign in [-1,1]:
            change=sign*epsilon;trial=c.copy();trial[32+col]+=change
            def equations(w):
                cc=trial.copy();cc[chosen]+=w[20:];cc[:8]+=vev**2*portals
                return np.r_[potential(w[:20],cc,P)[1],source_eigenvalues(w[:20])-baseline_eigen]
            initial=np.r_[x+change*FIX[:,col],change*DCC[:,col]]
            solution=root(equations,initial,tol=1e-10);xx=solution.x[:20]
            residual=float(np.max(abs(equations(solution.x))));assert residual<1e-9
            rr,ss,_=frame_and_spectrum(np.r_[xx,z[20]])
            cc=trial.copy();cc[chosen]+=solution.x[20:]
            mm=2*lam*vev**2+operators(xx,P)[0][:8]@portals
            hh=hessian(lambda zz:joint_higgs(zz,cc,P,portals,mm,lam),np.r_[xx,z[20]])
            sides.append({'sign':sign,'equation_residual':residual,'observables':rr,
                          'hessian_min':float(np.linalg.eigvalsh(hh)[0]),
                          'maximum_mass_change':float(max(np.max(abs(s['masses']-base['masses'])) for s,base in zip(ss,sectors)))})
        fd=(np.array(sides[1]['observables']['squared_magnitudes'])-np.array(sides[0]['observables']['squared_magnitudes']))/(2*epsilon)
        finite.append({'operator_index':int(col),'operator':MIXED_NAMES[col],'sides':sides,
                       'finite_response':fd.tolist(),'implicit_response':RF[:,col].tolist(),
                       'relative_response_error':float(np.linalg.norm(fd-RF[:,col])/max(np.linalg.norm(RF[:,col]),1e-30))})
    F=np.array([v['finite_response'] for v in finite]).T
    IF=np.array([v['implicit_response'] for v in finite]).T
    finite_rank={'singular_values':np.linalg.svd(F,compute_uv=False).tolist(),
                 'implicit_singular_values':np.linalg.svd(IF,compute_uv=False).tolist(),
                 'response_discrepancy_spectral_norm':float(np.linalg.norm(F-IF,2)),
                 'finite_response_determinant':float(np.linalg.det(F)),
                 'scope':'Numerical finite/implicit agreement, not an interval-arithmetic proof.'}
    assert finite_rank['response_discrepancy_spectral_norm']<finite_rank['singular_values'][-1]
    # Physical scalar Hessian eigenmodes mix eta, nonet and Higgs freely.
    loop=[];spectra=[]
    for f,spectrum in enumerate(sectors):
        vertices=np.zeros((21,6,6),complex);j=10*f
        vertices[j,3:,:3]=.1*np.eye(3);vertices[j+1,3:,:3]=.7*np.eye(3)
        vertices[j+2:j+10,3:,:3]=.8*BASIS
        vertices[20,:3,:3]=[1.2,.57][f]*np.eye(3)/np.sqrt(2)
        rotated=np.einsum('ik,ijl->kjl',O,vertices)
        loop.append(paired_vertex_reality(spectrum,rotated))
        q=np.linalg.norm(spectrum['doublet_frame'],axis=0)
        spectra.append({'masses':spectrum['masses'].tolist(),'doublet_weights':q.tolist(),
                        'tree_mass_determinant_real':float(np.linalg.det(spectrum['mass_matrix']).real),
                        'tree_mass_determinant_imag':float(np.linalg.det(spectrum['mass_matrix']).imag)})
    # Independence and group covariance tests evaluate the whole 60-vector.
    rng=np.random.default_rng(7781);samples=np.array([operators(rng.normal(size=20),P)[0] for _ in range(160)])
    rank=int(np.linalg.matrix_rank(samples,tol=1e-7));assert rank==60
    import sympy as sy
    cp=json.loads((ROOT/'receipts/m22_interactions/valentiner_cp.json').read_text())
    Xcp=np.array([[complex(sy.sympify(t).evalf()) for t in row] for row in cp['unitary_CP_matrix']])
    C=np.einsum('aij,jk,bkl,il->ab',BASIS,Xcp,BASIS.conj(),Xcp.conj()).real
    def transform(v,D):
        v=v.copy();v[2:10]=D@v[2:10];v[12:]=D@v[12:];return v
    cp_error=float(np.max(abs(operators(transform(x,C),P)[0]-values)))
    partner=np.r_[transform(x,C),z[20]];partner_obs=frame_and_spectrum(partner)[0]
    group_error=float(max(np.max(abs(operators(transform(x,adjoint(numeric(g))),P)[0]-values)) for g in generators()))
    result={'scope':'Complete renormalizable scalar potential for the new minimal real nonet pair and Higgs. Local numerical branch; no global-minimum certificate or observed CKM fit.',
      'operator_census':exact_operator_census(),'CP_adjoint_matrix':C.tolist(),
      'CP_partner':{'energy':fun(partner)[0],'gradient_norm':float(np.linalg.norm(fun(partner)[1])),'observables':partner_obs},'projector_certificate':pcert,'operator_names':OPERATOR_NAMES,
      'coefficients':c.tolist(),'Higgs_portals':portals.tolist(),'Higgs_mu2':float(mu2),'Higgs_lambda':lam,
      'quartic_lower_bound_without_Higgs':float(1/6-.12),
      'joint_quartic_total_norm_lower_bound':.01625,
      'quartic_bound_proof':'Six unit radial quartics give norm20^4/6, remaining coefficient absolute sum is .12. Each portal singlet 2x2 form and adjoint norm coefficient is positive. Higgs lambda*h^4/4 gives a combined lower bound min(7/150,.13/4)/2.',
      'scan':scan,'selection_rule':'First locally stable, nondegenerate branch with |J|>1e-5; no target angle or CKM magnitude used.',
      'selected_seed':20261006+index,'selected_start':start,'canonical_coordinates':z.tolist(),
      'energy':fun(z)[0],'gradient_norm':float(np.linalg.norm(fun(z)[1])),
      'scalar_hessian_eigenvalues':evals.tolist(),'neutral_physical_scalar_count':21,
      'observables':obs,'fermion_coefficients_per_sector':[[1.2,1.,.1,.7,.8],[.57,1.,.1,.7,.8]],
      'fermion_spectra':spectra,'maximum_one_loop_paired_vertex_imaginary_part':max(loop),
      'one_loop_scope':'First-order mass-phase theorem for the complete declared renormalizable Hermitian fermion action; no two-loop or higher-dimensional guarantee.',
      'scalar_operator_evaluation_rank':rank,'operator_CP_error':cp_error,'operator_generator_error':group_error,
      'unconstrained_mixed_response_singular_values':np.linalg.svd(R,compute_uv=False).tolist(),
      'fixed_spectrum_compensating_quadratics':[OPERATOR_NAMES[i] for i in chosen],
      'fixed_spectrum_compensator_singular_values':np.linalg.svd(T,compute_uv=False).tolist(),
      'fixed_spectrum_response_singular_values':np.linalg.svd(RF,compute_uv=False).tolist(),
      'fixed_spectrum_linear_error':float(np.max(abs(E@FIX))),
      'fixed_spectrum_finite_checks':finite,'fixed_spectrum_finite_rank_check':finite_rank,'geometry':exact_geometry_certificate(),'trace_potential_certificate':exact_trace_potential_certificate(),
      'rational_elliptic_example':elliptic_slice(Q(1,100000),Q(73,500)),
      'conclusion':'All four unitary mixing observables remain locally adjustable at fixed six quark masses. This full scalar symmetry does not enforce the golden or 66-degree target relations.'}
    assert evals[0]>0 and result['gradient_norm']<1e-10 and max(loop)<1e-12
    return result


def main():
    result=build();OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ['selected_seed','selected_start','energy','gradient_norm','observables','fixed_spectrum_response_singular_values','maximum_one_loop_paired_vertex_imaginary_part']},indent=2))

if __name__=='__main__':main()
