"""Low-degree CP covariants and Hermitian Nelson--Barr mixing.

Hermiticity is a property of a real scalar nonet, not an equality between
independent complex-field Yukawa coefficients. Calibration coefficients
are explicit inputs. The one-loop mass-phase theorem does not predict CKM.
"""
import numpy as np
import mpmath as mp
from .flavor_kinetic import matrix,array,hermitian_coordinates

WORD_NAMES=['I','R','R2','T','RT+TR','R2T+TR2','T2','RT2+T2R','RT2R']
FIELD_DEGREES=[0,2,4,2,4,6,4,6,8]


def words(R,T):
    if isinstance(R,mp.matrix):I=mp.eye(3)
    else:I=np.eye(3)
    return [I,R,R@R,T,R@T+T@R,R@R@T+T@R@R,T@T,
            R@T@T+T@T@R,R@T@T@R]


def coordinate_matrix(R,T):
    return mp.matrix([[v for v in hermitian_coordinates(Q)] for Q in words(R,T)]).T


def polynomial_calibration(R,T,target,digits=90):
    with mp.workdps(digits):
        R,T,target=matrix(R),matrix(T),matrix(target)
        R,T,target=(R+R.H)/2,(T+T.H)/2,(target+target.H)/2
        W=coordinate_matrix(R,T);coefficients=mp.lu_solve(W,hermitian_coordinates(target))
        fitted=sum((a*Q for a,Q in zip(coefficients,words(R,T))),mp.zeros(3))
        error=max(abs(fitted[i,j]-target[i,j]) for i in range(3) for j in range(3))
        return {'coefficients':[mp.nstr(a,80) for a in coefficients],
                'target_error':float(error),'coordinate_determinant':mp.nstr(mp.det(W),65),
                'maximum_absolute_coefficient':float(max(abs(a) for a in coefficients)),
                'matrix':array(fitted)}


def evaluate_polynomial(R,T,coefficients,digits=90):
    with mp.workdps(digits):
        R,T=matrix(R),matrix(T);R,T=(R+R.H)/2,(T+T.H)/2
        return array(sum((mp.mpf(str(a))*Q for a,Q in zip(coefficients,words(R,T))),mp.zeros(3)))


def source_for_light_masses(masses,y,messenger_mass,vev):
    masses=np.asarray(masses,float);a=y*vev;m=messenger_mass
    if len(masses)!=3 or min(masses)<=0 or max(masses)>=min(a,m):
        raise ValueError('Three positive light masses below both a and m required')
    return np.sqrt((a*a-masses*masses)*(m*m-masses*masses))/masses


def doublet_weights(masses,y,messenger_mass,vev):
    masses=np.asarray(masses,float);a=y*vev;m=messenger_mass;lam=masses**2
    return np.sqrt(a*a*(m*m-lam)/(a*a*m*m-lam*lam))


def nb_matrix(C,y,messenger_mass,vev):
    C=np.asarray(C,complex)
    if C.shape!=(3,3) or np.max(abs(C-C.conj().T))>1e-8*max(np.linalg.norm(C),1):
        raise ValueError('Hermitian three-family mixing matrix required')
    if min(y,messenger_mass,vev)<=0:raise ValueError('Positive real scales required')
    return np.block([[vev*y*np.eye(3),np.zeros((3,3))],[C,messenger_mass*np.eye(3)]])


def block_spectrum(C,y,messenger_mass,vev):
    """Diagonalize real two-state blocks without a hierarchical 6x6 SVD."""
    C=np.asarray(C,complex);D=nb_matrix(C,y,messenger_mass,vev)
    values,U=np.linalg.eigh((C+C.conj().T)/2);left=[];right=[];masses=[]
    for h,u in zip(values,U.T):
        # U.T rows are the eigenvector columns, without conjugation.
        a,sv,b=np.linalg.svd(np.array([[vev*y,0.],[h,messenger_mass]]))
        # The small singular value is the determinant divided by the large
        # one. This avoids subtractive loss in a hierarchical two-state SVD.
        sv[1]=vev*y*messenger_mass/sv[0]
        for j in range(2):
            masses.append(sv[j]);left.append(np.r_[a[0,j]*u,a[1,j]*u]);right.append(np.r_[b[j,0]*u,b[j,1]*u])
    order=np.argsort(masses);L=np.column_stack(left)[:,order];V=np.column_stack(right)[:,order]
    mass=np.array(masses)[order];Q=L[:3,:3]
    return {'mass_matrix':D,'masses':mass,'left':L,'right':V,'doublet_frame':Q,
            'neutral_current':Q.conj().T@Q,'source_eigenvalues':values,'source_eigenvectors':U}


def nonet_target(C,singlet_coupling=.7,adjoint_coupling=.8,eta_coupling=.1):
    C=np.asarray(C,complex);singlet=np.trace(C).real/3*np.eye(3)
    return (singlet-eta_coupling*np.eye(3))/singlet_coupling+(C-singlet)/adjoint_coupling


def nonet_mix(H,eta=1.,singlet_coupling=.7,adjoint_coupling=.8,eta_coupling=.1):
    H=np.asarray(H,complex);singlet=np.trace(H).real/3*np.eye(3)
    return singlet_coupling*singlet+adjoint_coupling*(H-singlet)+eta_coupling*eta*np.eye(3)


def neutral_vertices(basis,y,singlet_coupling=.7,adjoint_coupling=.8,eta_coupling=.1):
    """Canonical real nonet, odd real singlet and neutral Higgs vertices."""
    basis=np.asarray(basis,complex);G=np.zeros((len(basis)+2,6,6),complex)
    for i,Q in enumerate(basis):
        singlet=np.trace(Q).real/3*np.eye(3)
        G[i,3:,:3]=singlet_coupling*singlet+adjoint_coupling*(Q-singlet)
    G[-2,3:,:3]=eta_coupling*np.eye(3);G[-1,:3,:3]=y*np.eye(3)/np.sqrt(2)
    return G


def paired_vertex_reality(spectrum,vertices):
    G=np.einsum('ij,ajk,kl->ail',spectrum['left'].conj().T,vertices,spectrum['right'])
    products=G*np.swapaxes(G,1,2)
    scale=max(float(np.max(abs(products))),1.)
    return float(np.max(abs(products.imag))/scale)
