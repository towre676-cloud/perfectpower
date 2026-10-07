"""Canonical three-field wall and conforming finite-element fluctuations.

The scalar reference factorization is exact. The coupled BVP and finite-box
eigenvalues are numerical: convergence is evidence, not a continuum certificate.
Only the radial Higgs and the two spectator fields are included.
"""
from dataclasses import dataclass
from math import sqrt
import numpy as np
from scipy.integrate import solve_bvp, quad
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh
from scipy.linalg import cholesky_banded


@dataclass(frozen=True)
class HiggsWall:
    portal: float = 1e-7
    lam: float = .13
    v_GeV: float = 246.

    def __post_init__(self):
        if not all(np.isfinite(z) for z in (self.portal,self.lam,self.v_GeV)) or self.portal<0 or min(self.lam,self.v_GeV)<=0:
            raise ValueError('nonnegative portal and positive finite Higgs inputs required')


def scalar_reference(model):
    k=model.v_GeV*sqrt(model.lam/2)
    return {'k_GeV':k,'translation_eigenvalue_GeV2':0.,
            'shape_eigenvalue_GeV2':3*k*k,'shape_mass_GeV':sqrt(3)*k,
            'source_continuum_threshold_GeV2':4*k*k,
            'factorization':'L/k^2=(-d/dx+2*tanh(x))*(d/dx+2*tanh(x)); x=k*z.',
            'modes':'translation sech(x)^2, eigenvalue 0; shape sech(x)*tanh(x), eigenvalue 3; continuum [4,infinity).',
            'scope':'Exact decoupled scalar reference; the Higgs continuum can embed the shape mode when a portal is present.'}


def potential_and_hessian(model,bath,u,y,h):
    """V/v^4 and its Hessian in (phi/v,S/v,h_radial/v)."""
    a=model.current_g_GeV/model.v_GeV;m=model.heavy_mass_GeV/model.v_GeV
    h0=bath.v_GeV/model.v_GeV;b=bath.portal/bath.lam
    rs=y+a*u*u/m**2;rh=h*h-h0*h0+b*(u*u-1)
    V=model.lam*(u*u-1)**2/4+m*m*rs*rs/2+bath.lam*rh*rh/4
    H=np.array([[model.lam*(3*u*u-1)+2*a*rs+4*a*a*u*u/m**2+bath.portal*rh+2*bath.portal*b*u*u,2*a*u,2*bath.portal*u*h],
                [2*a*u,m*m,0.],
                [2*bath.portal*u*h,0.,bath.lam*(rh+2*h*h)]])
    return V,H


def solve_coupled_wall(model,bath=HiggsWall(),*,length_factor=12.,tol=2e-10,central_nodes=650):
    if model.bias_h0_GeV3:raise ValueError('static wall requires the unbiased degenerate potential')
    if length_factor<5 or tol<=0 or central_nodes<80:raise ValueError('resolved positive BVP controls required')
    k=sqrt(model.lam/2);m=model.heavy_mass_GeV/model.v_GeV;a=model.current_g_GeV/model.v_GeV
    h0=bath.v_GeV/model.v_GeV;mh=sqrt(2*bath.lam)*h0;beta=bath.portal/bath.lam
    L=max(length_factor/k,length_factor/mh);core=min(18/k,L)
    tail=np.geomspace(core,L,180) if L-core>1e-12*L else np.array([])
    grid=np.unique(np.r_[np.linspace(0,core,central_nodes),tail])
    u=np.tanh(k*grid);p=k*(1-u*u);y=-a*u*u/m**2;q=-2*a*u*p/m**2
    amplitude=bath.portal*h0/(k*mh)
    h=h0+amplitude*np.exp(-mh*grid);r=-mh*amplitude*np.exp(-mh*grid)
    def equations(x,z):
        u,y,h,p,q,r=z;rs=y+a*u*u/m**2;rh=h*h-h0*h0+beta*(u*u-1)
        return np.array([p,q,r,model.lam*u*(u*u-1)+2*a*u*rs+bath.portal*u*rh,m*m*rs,bath.lam*h*rh])
    def boundaries(z0,zL):return np.array([z0[0],z0[4],z0[5],zL[0]-1,zL[1]+a/m**2,zL[2]-h0])
    sol=solve_bvp(equations,boundaries,grid,np.array([u,y,h,p,q,r]),tol=tol,max_nodes=40000)
    if not sol.success:raise ArithmeticError(sol.message)
    def density(x):
        z=sol.sol(x);V=potential_and_hessian(model,bath,*z[:3])[0]
        return np.dot(z[3:],z[3:])/2+V
    pieces=[quad(density,lo,hi,epsabs=1e-13,epsrel=2e-11,limit=300) for lo,hi in [(0,core),(core,L)]]
    sample=np.unique(np.r_[np.linspace(0,core,401),np.geomspace(core,L,100)])
    z=sol.sol(sample)
    error=max(abs(np.dot(v[3:],v[3:])/2-potential_and_hessian(model,bath,*v[:3])[0]) for v in z.T)
    profile={'rho':sample.tolist(),'phi_over_v':z[0].tolist(),'S_over_v':z[1].tolist(),'radial_Higgs_GeV':(z[2]*model.v_GeV).tolist()}
    report={'tension_GeV3':2*sum(v[0] for v in pieces)*model.v_GeV**3,
            'quadrature_error_GeV3':2*sum(v[1] for v in pieces)*model.v_GeV**3,
            'half_box_rho':L,'central_Higgs_GeV':float(z[2,0]*model.v_GeV),
            'maximum_BVP_relative_residual':float(max(sol.rms_residuals)),
            'boundary_residual':float(max(abs(boundaries(sol.y[:,0],sol.y[:,-1])))),
            'first_integral_maximum_error':float(error),'profile':profile,
            'scope':'Unbiased three-field canonical static solution on a finite box; no gauge, angular Higgs, fermion or network fluctuations.'}
    return {'model':model,'bath':bath,'solution':sol,'L':L,'k':k,'report':report}


def _fem(wall,parity,central_nodes,tail_nodes=160):
    """Quadratic conforming elements; five-point Gauss potential integration."""
    if parity not in ('translation','opposite'):raise ValueError('unknown CP/reflection parity sector')
    k=wall['k'];L=wall['L'];core=min(12/k,L)
    edges=np.unique(np.r_[np.linspace(0,core,central_nodes),np.geomspace(core,L,tail_nodes)])
    x=np.sort(np.r_[edges,(edges[:-1]+edges[1:])/2])
    n=len(x);rr=[];cc=[];kk=[];mm=[]
    gauss,weights=np.polynomial.legendre.leggauss(5)
    for j in range(len(edges)-1):
        d=edges[j+1]-edges[j]
        K=np.kron(np.array([[7,-8,1],[-8,16,-8],[1,-8,7]])/(3*d),np.eye(3))
        M=np.kron(d*np.array([[4,2,-1],[2,16,2],[-1,2,4]])/30,np.eye(3))
        for s,w in zip(gauss,weights):
            N=np.array([s*(s-1)/2,1-s*s,s*(s+1)/2]);rho=edges[j]+(s+1)*d/2
            z=wall['solution'].sol(rho)
            H=potential_and_hessian(wall['model'],wall['bath'],*z[:3])[1]
            K+=w*d/2*np.kron(np.outer(N,N),H)
        ids=np.arange(6*j,6*j+9)
        rr.extend(np.repeat(ids,9));cc.extend(np.tile(ids,9));kk.extend(K.ravel());mm.extend(M.ravel())
    K=coo_matrix((kk,(rr,cc)),shape=(3*n,3*n)).tocsr();M=coo_matrix((mm,(rr,cc)),shape=(3*n,3*n)).tocsr()
    # Right boundary is Dirichlet. Neumann conditions at zero are natural.
    excluded={3*n-3,3*n-2,3*n-1}
    excluded.update({1,2} if parity=='translation' else {0})
    keep=np.array([j for j in range(3*n) if j not in excluded]);K=K[keep][:,keep];M=M[keep][:,keep]
    reference=wall['solution'].sol(x)[3:].T.ravel()[keep]
    return x,K,M,reference


def fluctuation_spectrum(wall,*,central_nodes=700,eigenvalues=5,tail_nodes=160):
    if central_nodes<80 or eigenvalues<2 or tail_nodes<20:raise ValueError('resolved finite-element controls required')
    result={};vacH=potential_and_hessian(wall['model'],wall['bath'],1.,-wall['model'].current_g_GeV*wall['model'].v_GeV/wall['model'].heavy_mass_GeV**2,wall['bath'].v_GeV/wall['model'].v_GeV)[1]
    thresholds=np.linalg.eigvalsh(vacH)
    for parity in ('translation','opposite'):
        x,K,M,ref=_fem(wall,parity,central_nodes,tail_nodes)
        # A negative shift below the expected spectrum targets its bottom.
        # An additional SA solve is used in the tests for the scalar fixture.
        start=np.cos(.37*np.arange(K.shape[0]))+.1
        values,vectors=eigsh(K,k=eigenvalues,M=M,sigma=-.01,which='LM',tol=2e-10,v0=start)
        order=np.argsort(values);values=values[order];vectors=vectors[:,order]
        matrix_norm=float(np.max(np.asarray(abs(K).sum(axis=1))));mass_norm=float(np.max(np.asarray(abs(M).sum(axis=1))))
        residuals=[float(np.linalg.norm(K@q-e*M@q)/((matrix_norm+abs(e)*mass_norm)*np.linalg.norm(q))) for e,q in zip(values,vectors.T)]
        band=np.zeros((9,K.shape[0]))
        for d in range(9):band[d,:K.shape[0]-d]=K.diagonal(-d)
        try:cholesky_banded(band,lower=True,check_finite=False);positive=True
        except np.linalg.LinAlgError:positive=False
        overlaps=[min(1.,float(abs(q@(M@ref))/sqrt(float(ref@(M@ref))))) for q in vectors.T] if parity=='translation' else None
        rayleigh=float(ref@(K@ref)/(ref@(M@ref))) if parity=='translation' else None
        result[parity]={'eigenvalues_over_v2':values.tolist(),'eigenvalues_GeV2':(values*wall['model'].v_GeV**2).tolist(),
                        'normalized_backward_eigen_residuals':residuals,'translation_overlaps':overlaps,
                        'finite_matrix_Cholesky_positive':positive,
                        'translation_Rayleigh_over_v2':rayleigh,'degrees_of_freedom':K.shape[0],'mesh_nodes':len(x)}
    result.update({'vacuum_thresholds_over_v2':thresholds.tolist(),
                   'vacuum_particle_masses_GeV':(np.sqrt(thresholds)*wall['model'].v_GeV).tolist(),
                   'half_box_rho':wall['L'],'central_nodes':central_nodes,
                   'resolved_negative_modes':sum(e<0 for p in ('translation','opposite') for e in result[p]['eigenvalues_over_v2']),
                   'scope':'Finite-box quadratic Galerkin modes nearest a negative shift in both reflection sectors; floating banded Cholesky independently tests positivity of the whole discretized matrix. Neither check certifies exclusion of every continuum negative mode. The near-zero translation mode converges from a variational discretization; bulk Higgs modes are not extra localized wall states.'})
    return result
