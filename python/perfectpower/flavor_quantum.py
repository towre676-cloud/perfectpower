"""Neutral real-scalar chirality-flipping one-loop mass matching.

Canonical real scalar mass eigenmodes and the full Dirac spectrum are used.
The finite B0 convention is Delta - integral_0^1 log((t x+(1-t)y)/mu²).
delta D = - sum G_a D† B0(H_left,m_a²) G_a/(16 pi²).
Wavefunction terms are Hermitian and do not change the determinant phase.
"""
import numpy as np


def b0_finite(x,y,mu=1.):
    x,y=np.broadcast_arrays(np.asarray(x,float),np.asarray(y,float))
    if np.any(x<=0) or np.any(y<=0) or not np.isfinite(mu) or mu<=0:
        raise ValueError('Positive masses squared and renormalization scale required')
    d=(x-y)/y;result=np.empty_like(d)
    near=abs(d)<1e-4
    t=d[near]
    result[near]=-np.log(y[near]/mu**2)-t/2+t*t/6-t**3/12+t**4/20
    far=~near
    # Direct logarithms retain tiny x/y ratios which rounding d can erase.
    result[far]=1-(x[far]*np.log(x[far]/mu**2)-y[far]*np.log(y[far]/mu**2))/(x[far]-y[far])
    return result


def scalar_threshold(D,vertices,scalar_hessian,mu=1.):
    D=np.asarray(D,complex);vertices=np.asarray(vertices,complex);H=np.asarray(scalar_hessian,float)
    if D.ndim!=2 or D.shape[0]!=D.shape[1] or vertices.shape!=(len(H),*D.shape) or H.shape!=(len(H),len(H)):
        raise ValueError('Square Dirac matrix, matching real scalar Hessian and vertices required')
    masses2,O=np.linalg.eigh((H+H.T)/2)
    if min(masses2)<=0:raise ValueError('Stable positive scalar spectrum required')
    U,m,Vh=np.linalg.svd(D);V=Vh.conj().T
    if min(m)<=0:raise ValueError('Nonzero full Dirac spectrum required')
    G=np.einsum('ab,aij->bij',O,vertices)
    G=np.einsum('ij,ajk,kl->ail',U.conj().T,G,V)
    weights=m[None,:]*b0_finite(m[None,:]**2,masses2[:,None],mu)
    self_energy=-np.einsum('aik,ak,akj->aij',G,weights,G)/(16*np.pi**2)
    diagonal=np.diagonal(self_energy,axis1=1,axis2=2)
    contributions=np.imag(np.sum(diagonal/m[None,:],axis=1))
    divergence=-np.einsum('aik,k,aki,i->',G,m,G,1/m).imag/(16*np.pi**2)
    correction=np.sum(self_energy,axis=0)
    phase=np.angle(np.linalg.slogdet(np.diag(m)+correction)[0])
    return {'delta_theta':float(sum(contributions)),'mode_contributions':contributions,
            'UV_phase_coefficient':float(divergence),'scalar_masses_squared':masses2,
            'scalar_eigenvectors':O,'mass_basis_vertices':G,'fermion_masses':m,
            'mass_basis_correction':correction,'resummed_one_loop_matrix_phase':float(phase),
            'relative_correction_norm':float(np.linalg.norm(np.diag(1/m)@correction,2))}


def fermion_coleman_weinberg(D,mu=1.,colors=3):
    m=np.linalg.svd(D,compute_uv=False)
    if min(m)<=0 or mu<=0:raise ValueError('Positive masses and scale required')
    return float(-colors/(16*np.pi**2)*sum(m**4*(np.log(m*m/mu**2)-1.5)))


def fermion_CW_gradient(D,vertices,mu=1.,colors=3):
    """Canonical real-field gradient of the Dirac Coleman-Weinberg term."""
    U,m,Vh=np.linalg.svd(D)
    G=np.einsum('ij,ajk,kl->ail',U.conj().T,np.asarray(vertices),Vh.conj().T)
    weight=m**3*(np.log(m*m/mu**2)-1)
    return -colors/(4*np.pi**2)*np.einsum('ai,i->a',np.diagonal(G,axis1=1,axis2=2).real,weight)
