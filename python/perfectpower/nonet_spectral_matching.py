"""Exact tree momentum dependence of Gaussian scalar mediation.

z is a timelike mass squared. Formulae apply to the Hessian on the stationary
Gaussian valley; the finite pole solver assumes the source spectrum lies below
every mediator mass. This is scalar matching, not a quark kinetic theorem.
"""
import numpy as np
from scipy.linalg import eigh
from scipy.optimize import brentq


def _inputs(H,D,mass2):
    H=np.asarray(H,float);D=np.asarray(D,float);mass2=np.broadcast_to(np.asarray(mass2,float),(len(D),)).copy()
    if H.ndim!=2 or H.shape[0]!=H.shape[1] or D.ndim!=2 or D.shape[1]!=len(H):
        raise ValueError('Compatible real source Hessian and current Jacobian required')
    if np.any(mass2<=0) or not all(np.all(np.isfinite(x)) for x in [H,D,mass2]):
        raise ValueError('Finite data and positive mediator masses squared required')
    if np.max(abs(H-H.T))>1e-10:raise ValueError('Symmetric Hessian required')
    return H,D,mass2


def full_hessian(H,D,mass2):
    H,D,mass2=_inputs(H,D,mass2)
    return np.block([[H+D.T@(D/mass2[:,None]),D.T],[D,np.diag(mass2)]])


def effective_pencil(H,D,mass2,z):
    H,D,mass2=_inputs(H,D,mass2)
    if np.any(mass2==z):raise ValueError('Mediator pole excluded')
    K=np.eye(len(H))+D.T@(D/(mass2*(mass2-z))[:,None])
    return H-z*K


def tree_metric(D,mass2):
    D=np.asarray(D,float);mass2=np.broadcast_to(np.asarray(mass2,float),(len(D),))
    if np.any(mass2<=0):raise ValueError('Positive masses squared required')
    return np.eye(D.shape[1])+D.T@(D/mass2[:,None]**2)


def residue_metric(D,mass2,z):
    D=np.asarray(D,float);mass2=np.broadcast_to(np.asarray(mass2,float),(len(D),))
    if np.any(mass2==z):raise ValueError('Mediator pole excluded')
    return np.eye(D.shape[1])+D.T@(D/(mass2-z)[:,None]**2)


def finite_scalar_poles(H,D,mass2):
    H,D,mass2=_inputs(H,D,mass2);bare=np.linalg.eigvalsh(H)
    if bare[0]<=0 or bare[-1]>=min(mass2):
        raise ValueError('Positive source spectrum below all mediator thresholds required')
    upper=bare[-1]+(min(mass2)-bare[-1])*1e-7
    roots=np.array([brentq(lambda z:np.linalg.eigvalsh(effective_pencil(H,D,mass2,z))[i],0.,upper,xtol=5e-15,rtol=1e-14) for i in range(len(H))])
    vectors=[];norm_residual=[]
    for i,z in enumerate(roots):
        w,U=np.linalg.eigh(effective_pencil(H,D,mass2,z));v=U[:,i]
        v/=np.sqrt(v@residue_metric(D,mass2,z)@v)
        full=np.r_[v,-(D@v)/(mass2-z)];vectors.append(full);norm_residual.append(abs(full@full-1))
    vectors=np.column_stack(vectors);HH=full_hessian(H,D,mass2);direct,U=np.linalg.eigh(HH)
    local=eigh(H,tree_metric(D,mass2),eigvals_only=True)
    projector_error=np.linalg.norm(vectors@vectors.T-U[:,:len(H)]@U[:,:len(H)].T)
    bound=bare/(1+np.linalg.norm(D,2)**2/(min(mass2)*(min(mass2)-bare[-1])))
    return {'bare_source_masses_squared':bare.tolist(),'two_derivative_EFT_masses_squared':local.tolist(),
      'exact_light_poles_squared':roots.tolist(),'full_UV_masses_squared':direct.tolist(),
      'light_pole_maximum_absolute_error':float(np.max(abs(roots-direct[:len(H)]))),
      'full_light_subspace_projector_error':float(projector_error),
      'eigenvector_residual':float(np.max(abs(HH@vectors-vectors*roots))),
      'full_norm_residual':float(max(norm_residual)),'full_orthogonality_residual':float(np.max(abs(vectors.T@vectors-np.eye(len(H))))),
      'rigorous_ordered_lower_bounds':bound.tolist(),'tree_metric_eigenvalues':np.linalg.eigvalsh(tree_metric(D,mass2)).tolist(),
      'maximum_two_derivative_relative_pole_error':float(np.max((local-roots)/roots)),
      'source_pole_weights':np.sum(vectors[:len(H)]**2,axis=0).tolist(),
      'scope':'Exact Gaussian tree scalar poles and residues in the below-threshold regime; numerical root and matrix evaluation. No quark metric, quantum vacuum or two-loop claim.'}


def exact_gaussian_spectral_certificate():
    import sympy as s
    h,d,M,z=s.symbols('h d M z',real=True);K=1+d*d/(M*M*(M*M-z));Z=1+d*d/(M*M-z)**2
    HH=s.Matrix([[h+d*d/M**2,d],[d,M*M]])
    assert s.simplify((HH-z*s.eye(2)).det()-(M*M-z)*(h-z*K))==0
    assert s.simplify(-s.diff(h-z*K,z)-Z)==0
    # The finite example independently verifies the determinant identity with
    # two source coordinates and three unequal heavy masses as a polynomial.
    H=s.Matrix([[3,s.Rational(1,3)],[s.Rational(1,3),2]])
    D=s.Matrix([[1,2],[2,-1],[1,1]]);B=s.diag(11,13,17);F=H+D.T*B.inv()*D-z*s.eye(2)-D.T*(B-z*s.eye(3)).inv()*D
    full=(H+D.T*B.inv()*D).row_join(D.T).col_join(D.row_join(B))
    assert s.cancel((full-z*s.eye(5)).det()-(B-z*s.eye(3)).det()*F.det())==0
    return {'exact_one_source_identity':True,'exact_unequal_three_mediator_polynomial_identity':True,
      'general_pencil':'H-z[I+D^T diag(1/(M_a^2 (M_a^2-z))) D]',
      'residue_metric':'I+D^T diag(1/(M_a^2-z)^2) D',
      'tree_kinetic_metric':'I+D^T diag(1/M_a^4) D',
      'light_pole_order':'lower_bound_i <= exact_i <= local_two_derivative_i <= bare_i',
      'tree_effective_action':'+J^T (M^2+Box)^(-1) J/2 in the Lagrangian; derivative expansion has positive kinetic (partial J)^2/(2 M^4)',
      'scope':'The displayed nonlocal sign uses a mostly-minus Minkowski Lagrangian; the static effective potential is -J^2/(2 M^2). General matrix identity follows by Schur complement.'}


def exact_gaussian_wall_certificate():
    import sympy as s
    t,g,v,M,lam=s.symbols('t g v M lam',positive=True);x=v*(2*t-1);S=-g*x*x/M**2
    W=lam*(x*x-v*v)**2/4;K=s.diff(x,t)**2+s.diff(S,t)**2
    bound=s.factor(2*s.integrate(W,(t,0,1))*s.integrate(K,(t,0,1)))
    expected=16*lam*v**6/s.Integer(15)*(1+4*g*g*v*v/(3*M**4))
    assert s.simplify(bound-expected)==0
    example=s.factor(bound.subs({g:1,v:1,M:3,lam:1}));assert example==s.Rational(3952,3645)
    return {'path':'x=v(2t-1), S=-g x^2/M^2','potential':'lambda(x^2-v^2)^2/4+M^2(S+g x^2/M^2)^2/2',
      'canonical_EFT_tension_squared':'8 lambda v^6/9',
      'valley_Cauchy_upper_squared':str(bound),'example_lower_squared':'8/9','example_upper_squared':str(example),
      'global_minima':'x=+-v, S=-g v^2/M^2, from simultaneous vanishing of positive squares',
      'scope':'Exact conditional Gaussian wall sandwich and fully classified dimensionless two-field example; not the quark flavor vacuum or a cosmological normalization.'}
