"""Exact angular/gauge operators and nonlinear channel checks for radial walls.

Quadratic block separation does not imply nonlinear stability. Gauge couplings
are declared inputs; finite profile screens are not interval certificates.
"""
from dataclasses import replace
from math import sqrt
import numpy as np
from scipy.integrate import solve_bvp,quad
from scipy.interpolate import CubicSpline
from .wall_embedded_states import localized_embedded_candidate
from .wall_fluctuations import solve_coupled_wall,potential_and_hessian


def exact_channel_identities():
    import sympy as sp
    u,y,h,p1,p2,p3,eta,kappa,H,h0,lam,alpha,mu=sp.symbols('u y h pi1 pi2 pi3 eta kappa lambda_H h0 lambda alpha mu')
    rr=(h+eta)**2+p1*p1+p2*p2+p3*p3
    V=lam*(u*u-1)**2/4+mu*mu*(y+alpha*u*u/mu**2)**2/2+H*(rr-h0*h0+kappa/H*(u*u-1))**2/4
    at={eta:0,p1:0,p2:0,p3:0}
    checks={}
    for i,p in enumerate([p1,p2,p3]):
        for field in [u,y,eta]:checks[f'angular_{i}_mixed_{field}']=sp.diff(V,p,field).subs(at)
        checks[f'angular_{i}_Ward_mass']=sp.diff(V,p,2).subs(at)-(H*(h*h-h0*h0)+kappa*(u*u-1))
    checks['source_Goldstone_cubic']=sp.diff(V,u,p1,p1).subs(at)-2*kappa*u
    checks['radial_Goldstone_cubic']=sp.diff(V,eta,p1,p1).subs(at)-2*H*h
    z=sp.Symbol('z');hh=sp.Function('h')(z);f=sp.Function('f')(z);a=sp.diff(hh,z)/hh
    D=lambda q:sp.diff(q,z)-a*q;Dad=lambda q:-sp.diff(q,z)-a*q
    checks['global_Goldstone_factorization']=Dad(D(f))+sp.diff(f,z,2)-sp.diff(hh,z,2)/hh*f
    L=lambda q:sp.diff(q,z)+a*q;Lad=lambda q:-sp.diff(q,z)+a*q
    checks['longitudinal_Proca_factorization']=Lad(L(f))+sp.diff(f,z,2)-(2*a*a-sp.diff(hh,z,2)/hh)*f
    # Conjugate the constrained Proca variable F=m^2 A_z to chi=F/m.
    checks['longitudinal_Proca_conjugation']=(-sp.diff(hh*f,z,2)+2*a*sp.diff(hh*f,z))/hh+sp.diff(f,z,2)-(2*a*a-sp.diff(hh,z,2)/hh)*f
    charge,A,dA,pi,dpi,dh,deta=sp.symbols('q A dA pi dpi dh deta')
    kinetic=((dh+deta+charge*A*pi)**2+(dpi-charge*A*(h+eta))**2)/2
    eps=sp.Symbol('eps')
    expansion=sp.expand(kinetic.subs({A:eps*A,pi:eps*pi,dpi:eps*dpi,deta:eps*deta,eta:eps*eta})).coeff(eps,2)
    checks['radial_vector_quadratic_zero']=sp.diff(expansion,eta,A)
    checks['radial_derivative_vector_quadratic_zero']=sp.diff(expansion,deta,A)
    checks['Goldstone_vector_derivative_block']=sp.expand(expansion).coeff(charge,1)-A*(pi*dh-h*dpi)
    # Local cubic Ward identity follows from the static and radial equations.
    E,ph,pdd,hdd=sp.symbols('E psi_H psi_H_dd h_dd')
    Vg=H*(h*h-h0*h0)+kappa*(u*u-1);Vhh=Vg+2*H*h*h
    radial_source=E*ph+pdd-Vhh*ph
    goldstone_force=radial_source/h+2*H*h*ph
    checks['cubic_Ward_identity']=goldstone_force-(E*ph+pdd-Vg*ph)/h
    g,gp=sp.symbols('g gprime')
    neutral=h*h*sp.Matrix([[g*g,-g*gp],[-g*gp,gp*gp]])/4
    photon=sp.Matrix([gp,g])
    checks['photon_mass_null']=neutral.det()
    checks['photon_radial_mass_vertex_zero']=(photon.T*neutral.diff(h)*photon)[0]
    checks['neutral_mass_trace']=sp.trace(neutral)-(g*g+gp*gp)*h*h/4
    reduced={n:sp.factor(v) for n,v in checks.items()}
    if any(v!=0 for v in reduced.values()):raise ArithmeticError('channel algebra mismatch')
    return {n:str(v) for n,v in reduced.items()}


def candidate_channel_solution(model,bath,*,tune='source_lambda',length=22.,tol=1e-10):
    """Reconstruct a real radial candidate mode for independent Ward integrals."""
    c=localized_embedded_candidate(model,bath,tune=tune,length=length,tol=tol)
    m=replace(model,lam=c['tuned_source_lambda']);b=replace(bath,lam=c['tuned_Higgs_lambda'])
    wall=solve_coupled_wall(m,b,length_factor=length,tol=tol)
    k=wall['k'];R=k*wall['L'];x=np.linspace(0,R,850)
    interp=CubicSpline(np.array(c['profile']['rho'])*k,np.array([c['profile'][n] for n in ['source_mode','singlet_mode','Higgs_mode']]).T)
    guess=k*np.vstack((interp(x).T,interp(x,1).T))
    # Work in x=k*rho, preserving original candidate mode normalization.
    def rhs(x,z,e):
        values=wall['solution'].sol(x/k)
        matrices=np.array([potential_and_hessian(m,b,*v)[1] for v in values[:3].T])/k**2
        return np.vstack((z[3:],np.einsum('nij,jn->in',matrices,z[:3])-e[0]*z[:3]))
    h0=b.v_GeV/m.v_GeV;alpha=m.current_g_GeV/m.v_GeV;mu=m.heavy_mass_GeV/m.v_GeV
    threshold,U=np.linalg.eigh(potential_and_hessian(m,b,1,-alpha/mu**2,h0)[1]/k**2)
    def bc(a,z,e):
        decay=np.sqrt(threshold[1:]-e[0])
        return np.r_[a[0],a[4],a[5],a[3]-1,U[:,0]@z[:3],U[:,1:].T@z[3:]+decay*(U[:,1:].T@z[:3])]
    sol=solve_bvp(rhs,bc,x,guess,p=[c['energy_over_v2']/k**2],tol=tol,max_nodes=30000)
    if not sol.success:raise ArithmeticError(sol.message)
    return {'candidate':c,'wall':wall,'mode':sol,'mode_amplitude_scale':k,'mode_energy_over_v2':float(sol.p[0]*k*k),
        'open_endpoint_derivative_over_x':float(U[:,0]@sol.y[3:,-1]/k),
        'maximum_mode_residual':float(max(sol.rms_residuals))}


def analyze_channels(solution,*,g=.65,gprime=.36):
    if not all(np.isfinite(t) and t>0 for t in [g,gprime]):raise ValueError('positive finite declared gauge couplings required')
    wall=solution['wall'];mode=solution['mode'];model=wall['model'];bath=wall['bath'];k=wall['k'];R=wall['L']
    h0=bath.v_GeV/model.v_GeV;alpha=model.current_g_GeV/model.v_GeV;mu=model.heavy_mass_GeV/model.v_GeV
    E=solution['mode_energy_over_v2'];v=model.v_GeV
    def integral(f):return 2*quad(f,0,R,epsabs=1e-10,epsrel=2e-10,limit=300)[0]
    norm=integral(lambda rho:float(np.dot(mode.sol(k*rho)[:3]/k,mode.sol(k*rho)[:3]/k)))
    def profiles(rho):return wall['solution'].sol(rho),mode.sol(k*rho)/k
    def gg(rho):
        a,p=profiles(rho);u,h=a[0],a[2]
        return 2*bath.portal*u*p[0]+2*bath.lam*h*p[2]
    direct=integral(lambda rho:gg(rho)*(wall['solution'].sol(rho)[2]/h0)**2)
    moment=E/h0**2*integral(lambda rho:wall['solution'].sol(rho)[2]*(mode.sol(k*rho)[2]/k))
    a,p=profiles(R);boundary=2*(a[2]*k*p[5]-a[5]*p[2])/h0**2
    zero_energy_global_form=sqrt(v/norm)*direct
    # The VV Hessian coupling is d m_V^2/dh times the radial mode.
    radial_moment=integral(lambda rho:wall['solution'].sol(rho)[2]*(mode.sol(k*rho)[2]/k))
    W=sqrt(v/norm)*(g*g/2)*radial_moment
    Z=sqrt(v/norm)*((g*g+gprime*gprime)/2)*radial_moment
    rho=np.linspace(0,R,1001);background=wall['solution'].sol(rho);u,h=background[0],background[2];hp=background[5]
    VG=bath.lam*(h*h-h0*h0)+bath.portal*(u*u-1)
    hdd=h*VG;a=hp/h
    mW=g*bath.v_GeV/2;mZ=sqrt(g*g+gprime*gprime)*bath.v_GeV/2;mass=sqrt(E)*v
    factor_W=g*g*h*h/4;factor_Z=(g*g+gprime*gprime)*h*h/4
    return {'declared_g':g,'declared_gprime':gprime,'mass_GeV':mass,'W_vacuum_mass_GeV':mW,'Z_vacuum_mass_GeV':mZ,
        'two_W_threshold_GeV':2*mW,'two_Z_threshold_GeV':2*mZ,
        'bulk_WW_pair_open':bool(mass>2*mW),'bulk_ZZ_pair_open':bool(mass>2*mZ),
        'minimum_sampled_Higgs_ratio_to_vacuum':float(min(h/h0)),
        'minimum_sampled_source':float(min(u)),'maximum_sampled_source':float(max(u)),
        'sampled_profile_supports_positive_Higgs_barrier':bool(min(h)>0 and min(h/h0)>=1-1e-10 and max(abs(u))<=1+1e-10),
        'global_Goldstone_Ward_form_factor_direct':direct,'global_Goldstone_Ward_form_factor_from_mode':moment+boundary,
        'global_Goldstone_Ward_boundary_term':float(boundary),
        'global_Goldstone_Ward_relative_error':abs(direct-moment-boundary)/max(abs(direct),1e-30),
        'global_Goldstone_zero_energy_pair_overlap_GeV_half':zero_energy_global_form,
        'W_mass_vertex_integrated_form_factor_GeV_half':W,'Z_mass_vertex_integrated_form_factor_GeV_half':Z,
        'mode_full_line_norm_over_rho':norm,'open_endpoint_derivative_over_x':solution['open_endpoint_derivative_over_x'],
        'maximum_reconstructed_mode_residual':solution['maximum_mode_residual'],
        'profile':{'rho':rho.tolist(),'Higgs_ratio_to_vacuum':(h/h0).tolist(),
            'global_Goldstone_potential_over_v2':VG.tolist(),
            'W_transverse_potential_over_v2':factor_W.tolist(),
            'W_longitudinal_potential_over_v2':(factor_W+2*a*a-hdd/h).tolist(),
            'Z_transverse_potential_over_v2':factor_Z.tolist(),
            'Z_longitudinal_potential_over_v2':(factor_Z+2*a*a-hdd/h).tolist()},
        'quadratic_radial_angular_gauge_mixing':'Exactly zero on the real Higgs background; the separate Goldstone-longitudinal derivative block is retained.',
        'conditional_spectral_bound':'For a positive Higgs background with h>=h0, both transverse and physical longitudinal Proca operators have spectrum bounded below by their vacuum mass squared. Sampled profile checks do not certify the hypotheses.',
        'global_Goldstone_scope':'Ungauged O(4) diagnostic. The three massless angular fields are not extra physical particles after electroweak gauging. Zero-energy continuum overlaps are not on-shell decay widths.',
        'nonlinear_scope':'Nonzero cubic GG and VV vertices remain. No off-shell VV*, loop photon, fermion or complete nonlinear decay calculation. Fixed gauge inputs are benchmarks, not experimentally matched couplings.'}
