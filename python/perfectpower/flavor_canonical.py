"""Canonical tree matching, including the physical weak currents.

F is the full-rank n by (n+3) singlet-messenger mass row, with an
invertible last-n-column mass block. T is the
three-doublet Higgs row in the same right-handed basis. Canonical bare
fermion metrics and electroweak singlet messengers are explicit assumptions.
No unitary CKM parametrization is used at finite Higgs expectation value.
"""
from itertools import combinations
import numpy as np
from .flavor_mediator import inverse_sqrt


def dagger(a):
    return np.asarray(a, complex).conj().T


def hermitian(a):
    return (a+dagger(a))/2


def canonical_kernel(F, T):
    F, T = np.asarray(F, complex), np.asarray(T, complex)
    if F.ndim != 2 or F.shape[1] != F.shape[0]+3 or T.shape != (3,F.shape[1]):
        raise ValueError('F must have n rows and n+3 columns; T must have three rows')
    gap = float(np.linalg.svd(F, compute_uv=False)[-1])
    if gap <= 1e-13*np.linalg.norm(F,2):
        raise ValueError('Full-rank heavy row required')
    C, M = F[:,:3], F[:,3:]
    try:
        null = np.linalg.solve(M,C)
    except np.linalg.LinAlgError as exc:
        raise ValueError('Invertible square heavy mass block required') from exc
    E = np.vstack([np.eye(3),-null])@inverse_sqrt(hermitian(np.eye(3)+dagger(null)@null))
    Y = T@E
    G = F@dagger(F)
    X = np.linalg.solve(G,F@dagger(T))
    Z = hermitian(dagger(X)@X)
    return {'F':F,'T':T,'G':G,'null_frame':E,'Y':Y,
            'H0':hermitian(Y@dagger(Y)),'Z1':Z,'heavy_gap':gap}


def full_spectrum(kernel, vev):
    if not np.isfinite(vev) or vev <= 0:
        raise ValueError('Positive finite Higgs mass insertion required')
    D = np.vstack([vev*kernel['T'],kernel['F']])
    U, s, Vh = np.linalg.svd(D)
    U, s, Vh = U[:,::-1], s[::-1], Vh[::-1]
    Q = U[:3,:3]
    return {'mass_matrix':D,'masses':s,'left':U,'right':dagger(Vh),
            'doublet_frame':Q,'singlet_frame':U[3:,:3],
            'neutral_current':hermitian(dagger(Q)@Q),
            'doublet_loss':hermitian(np.eye(3)-Q@dagger(Q))}


def dimension_six(kernel, vev):
    K = np.eye(3)+vev**2*kernel['Z1']
    R = inverse_sqrt(K)
    U, values, _ = np.linalg.svd(R@kernel['Y'])
    U, values = U[:,::-1], values[::-1]
    return {'kinetic_metric':K,'masses':vev*values,
            'doublet_frame':R@U,'neutral_current':dagger(U)@np.linalg.inv(K)@U}


def current_pair(up, down):
    Nu, Nd = up['doublet_frame'], down['doublet_frame']
    V = dagger(Nu)@Nd
    rows = hermitian(np.eye(3)-V@dagger(V))
    columns = hermitian(np.eye(3)-dagger(V)@V)
    # Exact positive decomposition: intrinsic up loss plus missing down states.
    row_parts = [hermitian(np.eye(3)-dagger(Nu)@Nu),
                 hermitian(dagger(Nu)@(np.eye(3)-Nd@dagger(Nd))@Nu)]
    col_parts = [hermitian(np.eye(3)-dagger(Nd)@Nd),
                 hermitian(dagger(Nd)@(np.eye(3)-Nu@dagger(Nu))@Nd)]
    quartets = [{'rows':[i,k],'columns':[j,l],
                 'imaginary':float(np.imag(V[i,j]*V[k,l]*V[i,l].conjugate()*V[k,j].conjugate()))}
                for i,k in combinations(range(3),2) for j,l in combinations(range(3),2)]
    # This convention agrees with the legacy unitary J in the decoupling limit.
    J = float(np.imag(V[0,1]*V[1,2]*V[0,2].conjugate()*V[1,1].conjugate()))
    return {'V':V,'row_deficit':rows,'column_deficit':columns,
            'row_positive_parts':row_parts,'column_positive_parts':col_parts,
            'quartets':quartets,'CP_quartet':J}


def pole_certificate(kernel, spectrum, vev):
    G, F, T = kernel['G'],kernel['F'],kernel['T']
    residuals, norm_errors = [], []
    for i, mass in enumerate(spectrum['masses'][:3]):
        lam = mass**2
        if lam >= kernel['heavy_gap']**2:
            raise ValueError('Light pole must lie below the heavy gap')
        q = spectrum['doublet_frame'][:,i]
        X = np.linalg.solve(G-lam*np.eye(len(G)),F@dagger(T))
        r = -vev*X@q
        schur = vev**2*(T@dagger(T)-T@dagger(F)@X)@q-lam*q
        residuals.append(float(np.linalg.norm(schur)/max(vev**2*np.linalg.norm(T)**2,1e-300)))
        norm_errors.append(float(abs(np.vdot(q,q)+np.vdot(r,r)-1)))
    return {'normalized_Schur_residuals':residuals,'pole_metric_norm_errors':norm_errors}


def determinant_phase(M, unnormalized_Y):
    a, loga = np.linalg.slogdet(M)
    b, logb = np.linalg.slogdet(unnormalized_Y)
    return {'phase_factor':complex(a*b),'log_abs_coefficient':float(loga+logb),
            'phase':float(np.angle(a*b))}


def higgs_coupling(spectrum, T):
    """Derivative of the full Dirac mass matrix with respect to the real vev."""
    H = np.vstack([T,np.zeros_like(spectrum['mass_matrix'][3:])])
    return dagger(spectrum['left'])@H@spectrum['right']
