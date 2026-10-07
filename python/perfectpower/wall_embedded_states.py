"""Retuned radiation nodes: perturbative shift and finite-radius localized states.

A zero-open-channel finite-domain BVP is numerical evidence for an embedded
state candidate, not an infinite-domain existence theorem or symmetry protection.
"""
from dataclasses import replace
from math import sqrt,pi,cosh
import numpy as np
from scipy.integrate import solve_bvp,quad
from .wall_fluctuations import HiggsWall,solve_coupled_wall,potential_and_hessian


def leading_node_shift(*,radius_x=24.,tol=1e-10):
    """Universal first-order shift of m_H^2/v^2 at the g=0 radiation node.

    H solves (-d_x^2+2)H=sech(x)^2. Its cosine overlap determines the
    compensating threshold shift when the full background is distorted.
    """
    if radius_x<12 or tol<=0:raise ValueError('resolved Green-function controls required')
    x=np.linspace(0,radius_x,500)
    def rhs(x,z):return np.array([z[1],2*z[0]-1/np.cosh(x)**2])
    def bc(a,b):return np.array([a[1],b[1]+sqrt(2)*b[0]])
    sol=solve_bvp(rhs,bc,x,np.zeros((2,len(x))),tol=tol,max_nodes=10000)
    if not sol.success:raise ArithmeticError(sol.message)
    def integrand(x):
        s=1/cosh(x);H=sol.sol(x)[0]
        return ((8-2*s*s)*s*H-s**3)*np.cos(x)
    J,err=quad(integrand,0,radius_x,epsabs=1e-12,epsrel=1e-12,limit=200)
    J*=2;F=pi/cosh(pi/2);slope=-J/F
    return {'threshold_shift_per_portal':float(slope),'overlap_J':float(J),
            'sech_transform_at_one':F,'quadrature_error_in_slope':2*err/F,
            'radius_x':radius_x,'maximum_Green_BVP_relative_residual':float(max(sol.rms_residuals)),
            'relation':'2*lambda_H*h0^2=lambda+slope*kappa+O(kappa^2), for g=0 and fixed h0>0.',
            'scope':'Derived first-order retuning coefficient with numerical Green response/quadrature. No certified remainder bound.'}


def localized_embedded_candidate(model,bath,*,tune='Higgs_lambda',length=18.,tol=1e-9,max_nodes=30000):
    """Solve background, real mode, energy and Higgs quartic simultaneously.

    Center parity and normalization give four mode conditions. At the right
    endpoint both open-channel value and derivative vanish and two closed
    channels decay. The unknown quartic supplies the extra tuning parameter.
    The initial guess uses the scalar-node value of the chosen quartic.
    """
    if model.bias_h0_GeV3:raise ValueError('unbiased static wall required')
    if bath.portal<=0 or length<12 or tol<=0:raise ValueError('positive portal and resolved controls required')
    if tune not in ('Higgs_lambda','source_lambda'):raise ValueError('unknown tuned quartic')
    h0=bath.v_GeV/model.v_GeV
    if tune=='source_lambda':model=replace(model,lam=2*bath.lam*h0*h0)
    k=sqrt(model.lam/2)
    baseline=model.lam/(2*h0*h0) if tune=='Higgs_lambda' else model.lam
    def quartics(p):
        adjusted=baseline*np.exp(p[1])
        return (model.lam,adjusted) if tune=='Higgs_lambda' else (adjusted,bath.lam)
    if model.heavy_mass_GeV/model.v_GeV<=sqrt(3)*k:raise ValueError('heavy channel must remain closed')
    initial_bath=replace(bath,lam=baseline) if tune=='Higgs_lambda' else bath
    initial=solve_coupled_wall(model,initial_bath,length_factor=length)
    R=initial['L'];grid=np.linspace(0,R,650)
    source=np.tanh(k*grid);sech=1/np.cosh(k*grid)
    psi=np.zeros((3,len(grid)));der=psi.copy()
    psi[0]=sech*source/k;der[0]=sech*(1-2*source*source)
    psi[2]=bath.portal*h0*sech/k**3;der[2]=-bath.portal*h0*sech*source/k**2
    alpha=model.current_g_GeV/model.v_GeV;mu=model.heavy_mass_GeV/model.v_GeV
    psi[1]=-2*alpha*source*psi[0]/mu**2
    der[1]=-2*alpha*(k*sech*sech*psi[0]+source*der[0])/mu**2
    start=np.vstack((initial['solution'].sol(grid),psi,der))
    def operator(u,y,h,H,l):
        rs=y+alpha*u*u/mu**2;rh=h*h-h0*h0+bath.portal/H*(u*u-1)
        M=np.zeros((len(u),3,3))
        M[:,0,0]=l*(3*u*u-1)+2*alpha*rs+4*alpha*alpha*u*u/mu**2+bath.portal*rh+2*bath.portal**2/H*u*u
        M[:,0,1]=M[:,1,0]=2*alpha*u;M[:,1,1]=mu*mu
        M[:,0,2]=M[:,2,0]=2*bath.portal*u*h;M[:,2,2]=H*(rh+2*h*h)
        return M
    def rhs(x,z,p):
        E=p[0];l,H=quartics(p);u,y,h=z[:3]
        rs=y+alpha*u*u/mu**2;rh=h*h-h0*h0+bath.portal/H*(u*u-1)
        acceleration=np.array([l*u*(u*u-1)+2*alpha*u*rs+bath.portal*u*rh,mu*mu*rs,H*h*rh])
        modes=np.einsum('nij,jn->in',operator(u,y,h,H,l),z[6:9])-E*z[6:9]
        return np.vstack((z[3:6],acceleration,z[9:12],modes))
    def channels(p):
        l,H=quartics(p);V=potential_and_hessian(replace(model,lam=l),replace(bath,lam=H),1,-alpha/mu**2,h0)[1]
        values,U=np.linalg.eigh(V)
        for j in range(3):
            if U[np.argmax(abs(U[:,j])),j]<0:U[:,j]*=-1
        return values,U
    def bc(a,b,p):
        values,U=channels(p);E=p[0]
        # Iteration is local to the initial node with exactly one open channel.
        decays=np.sqrt(values[1:]-E)
        endpoint=np.r_[U[:,0]@b[6:9],U[:,0]@b[9:12],U[:,1:].T@b[9:12]+decays*(U[:,1:].T@b[6:9])]
        return np.r_[a[0],a[4],a[5],b[0]-1,b[1]+alpha/mu**2,b[2]-h0,
                     a[6],a[10],a[11],a[9]-1,endpoint]
    sol=solve_bvp(rhs,bc,grid,start,p=np.array([3*k*k,0.]),tol=tol,max_nodes=max_nodes)
    if not sol.success:raise ArithmeticError(sol.message)
    E=sol.p[0];l,H=quartics(sol.p);thresholds,U=channels(sol.p)
    if not thresholds[0]<E<thresholds[1]:raise ArithmeticError('candidate left one-open-channel domain')
    sample=np.linspace(0,R,401);values=sol.sol(sample);mode=values[6:9]
    n=quad(lambda x:float(np.dot(sol.sol(x)[6:9],sol.sol(x)[6:9])),0,R,epsabs=1e-9,limit=200)[0]
    endpoint=U.T@sol.y[6:9,-1];derivative=U.T@sol.y[9:12,-1]
    exterior_norm=float(np.sum(endpoint[1:]**2/np.sqrt(thresholds[1:]-E)))
    return {'tuned_parameter':tune,'tuned_Higgs_lambda':float(H),'tuned_source_lambda':float(l),'energy_over_v2':float(E),
            'mass_GeV':float(np.sqrt(E)*model.v_GeV),'thresholds_over_v2':thresholds.tolist(),
            'threshold_shift_from_scalar_node':float(2*H*h0*h0-l),
            'portal':bath.portal,'radius_rho':R,'initial_source_decay_lengths':k*R,
            'maximum_BVP_relative_residual':float(max(sol.rms_residuals)),
            'boundary_residual':float(max(abs(bc(sol.y[:,0],sol.y[:,-1],sol.p)))),
            'open_channel_endpoint_value':float(endpoint[0]),'open_channel_endpoint_derivative':float(derivative[0]),
            'closed_channel_endpoint_norm':float(np.linalg.norm(endpoint[1:])),
            'background_endpoint_derivative_norm':float(np.linalg.norm(sol.y[3:6,-1])),
            'constant_exterior_closed_tail_norm_fraction':exterior_norm/(2*n),
            'full_line_mode_norm_with_unit_source_derivative':2*n,
            'profile':{'rho':sample.tolist(),'source':values[0].tolist(),'radial_Higgs_over_v':values[2].tolist(),
                       'source_mode':mode[0].tolist(),'singlet_mode':mode[1].tolist(),'Higgs_mode':mode[2].tolist()},
            'scope':'Finite-radius jointly solved real localized embedded-state candidate, tuned by one declared quartic. Radius/tolerance continuation and independent outgoing poles are required; no infinite-domain existence or RG protection inferred.'}


def independent_green_node_shift(*,radius_x=24.):
    """Replay coefficient using the free Green convolution, without the BVP."""
    if radius_x<12:raise ValueError('resolved integration domain required')
    a=sqrt(2)
    def response(x):
        def f(y):return (np.exp(-a*abs(x-y))+np.exp(-a*(x+y)))/cosh(y)**2/(2*a)
        return quad(f,0,x,epsabs=1e-12,epsrel=1e-12)[0]+quad(f,x,radius_x,epsabs=1e-12,epsrel=1e-12)[0]
    def integrand(x):
        s=1/cosh(x);return ((8-2*s*s)*s*response(x)-s**3)*np.cos(x)
    overlap,error=quad(integrand,0,radius_x,epsabs=1e-11,epsrel=1e-11,limit=200)
    return {'threshold_shift_per_portal':float(-2*overlap/(pi/cosh(pi/2))),
            'outer_quadrature_error':2*error/(pi/cosh(pi/2)),
            'scope':'Independent explicit Green convolution and quadrature; numerical errors are not certified enclosures.'}
