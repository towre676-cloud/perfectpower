"""Physical response and loop-order diagnostics on the minimal nonet branch."""
import numpy as np
from scipy.optimize import root
from .nonet_potential import nonet_fields,BASIS
from .flavor_hermitian import words
from .flavor_quantum import scalar_threshold


def hermitian_coordinates(A):
    return np.r_[np.diag(A).real,[v for i,j in [(0,1),(0,2),(1,2)] for v in [np.sqrt(2)*A[i,j].real,np.sqrt(2)*A[i,j].imag]]]


def finite_metric_spectrum(C,y,vev,metric):
    w,U=np.linalg.eigh(metric)
    if min(w)<=0:raise ValueError('Positive quark metric required')
    inverse=(U/np.sqrt(w))@U.conj().T
    D=np.block([[vev*y*inverse,np.zeros((3,3))],[C@inverse,np.eye(3)]])
    L,m,R=np.linalg.svd(D);order=np.argsort(m);Q=L[:3,order[:3]]
    return m[order],Q,D


def finite_current_observables(Qu,Qd):
    V=Qu.conj().T@Qd
    return np.array([abs(V[0,1])**2,abs(V[1,2])**2,abs(V[0,2])**2,
              np.imag(V[0,1]*V[1,2]*V[0,2].conj()*V[1,1].conj())])


def kinetic_response(z):
    fields=nonet_fields(z[:20]);C=[.1*e*np.eye(3)+.7*s*np.eye(3)+.8*A for e,s,A in fields]
    R=fields[0][2]@fields[0][2];T=fields[1][2]@fields[1][2];W=words(R,T)
    matrix=np.column_stack([hermitian_coordinates(Q) for Q in W]);chi=float(np.trace(R@R@T@T@R@T).imag)
    singular=np.linalg.svd(matrix,compute_uv=False);det=float(np.linalg.det(matrix));expected=8*chi**3
    if abs(det-expected)>1e-8*max(abs(expected),1e-30):raise AssertionError('Covariant determinant identity failed')
    base=[finite_metric_spectrum(c,y,z[20]/np.sqrt(2),np.eye(3)) for c,y in zip(C,[1.2,.57])]
    _,U=np.linalg.eigh(C[1]);diag=[np.outer(u,u.conj()) for u in U.T];target=base[1][0][:3];step=2e-5;responses=[];checks=[]
    for Q in BASIS[:6]:
        sides=[]
        for sign in [-1,1]:
            B=np.eye(3)+sign*step*Q
            def equations(t):
                metric=B+sum((a*d for a,d in zip(t,diag)),np.zeros((3,3),complex))
                return finite_metric_spectrum(C[1],.57,z[20]/np.sqrt(2),metric)[0][:3]-target
            sol=root(equations,np.zeros(3),tol=1e-11);metric=B+sum((a*d for a,d in zip(sol.x,diag)),np.zeros((3,3),complex))
            masses,Qd,D=finite_metric_spectrum(C[1],.57,z[20]/np.sqrt(2),metric)
            if np.max(abs(masses[:3]-target))>1e-11:raise AssertionError('Finite light masses not retained')
            sides.append({'sign':sign,'physical_observables':finite_current_observables(base[0][1],Qd).tolist(),
              'maximum_light_mass_change':float(np.max(abs(masses[:3]-target))),
              'maximum_heavy_mass_change':float(np.max(abs(masses[3:]-base[1][0][3:]))),
              'metric_minimum':float(np.linalg.eigvalsh(metric)[0]),'tree_phase':float(np.angle(np.linalg.slogdet(D)[0]))})
        responses.append((np.array(sides[1]['physical_observables'])-np.array(sides[0]['physical_observables']))/(2*step));checks.append(sides)
    response=np.array(responses).T;row_norm=np.linalg.norm(response,axis=1);normalized=response/row_norm[:,None]
    return {'source_covariants':'R=A_u^2,T=A_d^2; both neutral under sector Z2 and CP compatible',
      'word_degrees':[0,2,4,2,4,6,4,6,8],'nine_word_determinant':det,'8_chi_cubed':expected,'chi':chi,
      'word_matrix_singular_values':singular.tolist(),'physical_response':response.tolist(),
      'row_normalized_response_singular_values':np.linalg.svd(normalized,compute_uv=False).tolist(),
      'finite_checks':checks,'positive_completion':'B=(I+sum real c_i Q_i)^2+epsilon I; epsilon>0, through degree sixteen',
      'scope':'All six finite light masses and the scalar vacuum retained. Heavy masses can change and are reported. Higher kinetic vertices are not covered by the renormalizable one-loop theorem.'}


def higher_order_phase_diagnostic(D,vertices,H):
    threshold=scalar_threshold(D,vertices,H);m=threshold['fermion_masses'];A=threshold['mass_basis_correction']/m[:,None]
    linear=float(np.trace(A).imag);quadratic=float(-np.trace(A@A).imag/2);full=threshold['resummed_one_loop_matrix_phase']
    return {'first_order_phase':linear,'quadratic_determinant_term':quadratic,'resummed_one_loop_matrix_phase':full,
      'correction_norm':float(np.linalg.norm(A,2)),'scope':'Quadratic expansion of the one-loop-corrected determinant only; omits genuine two-loop self energies and wavefunction matching. Not a complete two-loop strong-CP result.'}
