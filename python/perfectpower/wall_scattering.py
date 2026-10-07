"""Outgoing wall resonances and real-axis reflection for the radial spectator.

Numerical boundary-value solutions use the supplied canonical wall. Analytic
weak-portal widths refer to the decoupled scalar kink, not a cosmology rate.
"""
from math import pi,sqrt,cosh
import numpy as np
from scipy.integrate import solve_bvp,quad
from .wall_fluctuations import potential_and_hessian


def vacuum_channels(wall):
    m,b=wall['model'],wall['bath']
    H=potential_and_hessian(m,b,1.,-m.current_g_GeV*m.v_GeV/m.heavy_mass_GeV**2,b.v_GeV/m.v_GeV)[1]
    return np.linalg.eigh(H)


def outgoing_wavenumbers(energy,thresholds,open_channels):
    """Continue open square roots through the lower half-plane; closed decay."""
    energy=complex(energy)
    return np.array([np.sqrt(energy-t+0j) if op else 1j*np.sqrt(t-energy+0j)
                     for t,op in zip(thresholds,open_channels)])


def _mesh(wall,radius,energy):
    k=wall['k'];core=min(16/k,radius)
    # Resolve oscillatory outgoing Higgs waves and the core independently.
    q=sqrt(max(energy,1e-6))
    if radius-core<1e-12*radius:return np.linspace(0,radius,260)
    return np.unique(np.r_[np.linspace(0,core,260),np.linspace(core,radius,max(2,int((radius-core)*q*4)))])


def _potential(wall,x):
    u,y,h=wall['solution'].sol(x)[:3]
    m,b=wall['model'],wall['bath'];alpha=m.current_g_GeV/m.v_GeV;mu=m.heavy_mass_GeV/m.v_GeV
    beta=b.portal/b.lam;rs=y+alpha*u*u/mu**2;rh=h*h-(b.v_GeV/m.v_GeV)**2+beta*(u*u-1)
    H=np.zeros((len(x),3,3));H[:,0,0]=m.lam*(3*u*u-1)+2*alpha*rs+4*alpha*alpha*u*u/mu**2+b.portal*rh+2*b.portal*beta*u*u
    H[:,0,1]=H[:,1,0]=2*alpha*u;H[:,1,1]=mu*mu
    H[:,0,2]=H[:,2,0]=2*b.portal*u*h;H[:,2,2]=b.lam*(rh+2*h*h)
    return H


def outgoing_shape_pole(wall,*,radius=None,tol=1e-7,energy_guess=None,max_nodes=50000):
    """Mixed-parity pole with source odd and singlet/Higgs even.

    Normalize source derivative at rho=0 to one. Finite-radius outgoing
    conditions approximate the asymptotic problem; compare radii/tolerances.
    """
    radius=wall['L'] if radius is None else float(radius)
    if not 0<radius<=wall['L'] or tol<=0:raise ValueError('positive controls inside wall domain required')
    thresholds,U=vacuum_channels(wall)
    initial=3*wall['k']**2 if energy_guess is None else complex(energy_guess)
    opens=np.real(initial)>thresholds
    if not any(opens) or np.real(initial)>=thresholds[1]:raise ValueError('shape pole requires one open channel below source threshold')
    grid=_mesh(wall,radius,float(np.real(initial)));k=wall['k'];t=np.tanh(k*grid);sech=1/np.cosh(k*grid)
    psi=np.zeros((3,len(grid)),complex);der=psi.copy()
    psi[0]=sech*t/k;der[0]=sech*(1-2*t*t)
    def rhs(x,z,p):
        H=_potential(wall,x)
        return np.vstack((z[3:],np.einsum('nij,jn->in',H,z[:3])-p[0]*z[:3]))
    def bc(a,b,p):
        K=U@np.diag(1j*outgoing_wavenumbers(p[0],thresholds,opens))@U.T
        return np.r_[a[0],a[4],a[5],a[3]-1,b[3:]-K@b[:3]]
    guess=np.vstack((psi,der))
    def real_rhs(x,z,p):
        value=rhs(x,z[:6]+1j*z[6:],np.array([complex(*p)]))
        return np.vstack((value.real,value.imag))
    def real_bc(a,b,p):
        value=bc(a[:6]+1j*a[6:],b[:6]+1j*b[6:],np.array([complex(*p)]))
        return np.r_[value.real,value.imag]
    sol=solve_bvp(real_rhs,real_bc,grid,np.vstack((guess.real,guess.imag)),p=np.array([complex(initial).real,complex(initial).imag]),tol=tol,max_nodes=max_nodes)
    if not sol.success:raise ArithmeticError(sol.message)
    e=complex(*sol.p);frequency=np.sqrt(e+0j)*wall['model'].v_GeV
    def norm_density(x):
        z=sol.sol(x);return float(np.sum(abs(z[:3]+1j*z[6:9])**2))
    norm=quad(norm_density,0,radius,epsabs=1e-9,epsrel=1e-10,limit=200)[0]
    end=sol.y[:6,-1]+1j*sol.y[6:,-1]
    flux=float(np.imag(np.vdot(end[:3],end[3:])))
    expected=-e.imag*norm
    identity_error=abs(flux-expected)/max(abs(flux),abs(expected),1e-100)
    return {'energy_over_v2':[e.real,e.imag], 'mass_GeV':float(frequency.real),
            'width_GeV':float(-2*frequency.imag), 'radius_rho':radius,
            'maximum_BVP_relative_residual':float(max(sol.rms_residuals)),
            'boundary_residual':float(max(abs(real_bc(sol.y[:,0],sol.y[:,-1],sol.p)))),
            'mesh_nodes':len(sol.x),'open_channels':opens.tolist(),
            'scope':'Numerical finite-radius outgoing pole of the supplied radial three-field wall, continued on one open Higgs channel. No continuum stability certificate or network decay rate.',
            'finite_domain_outgoing_current':flux,
            'finite_domain_current_from_complex_energy':expected,
            'current_identity_relative_error':identity_error,
            'vacuum_matching_Hessian_error':float(np.linalg.norm(_potential(wall,np.array([radius]))[0]-U@np.diag(thresholds)@U.T))}


def weak_portal_shape_width(model,bath):
    """Leading portal-squared radiation width for the g=0 scalar reference.

    The normalized shape is sqrt(3k/2)*sech(k*rho)*tanh(k*rho).
    Its even Higgs source is 2*kappa*h0*tanh(k*rho)*shape.
    """
    k=sqrt(model.lam/2);h0=bath.v_GeV/model.v_GeV
    energy=3*k*k;threshold=2*bath.lam*h0*h0
    if threshold>=energy:return {'open':False,'width_GeV':0.,'form_factor':None}
    q=sqrt(energy-threshold);p=q/k
    form=0. if exact_shape_channel_conditions(model,bath)['leading_radiation_node'] else pi*(1-p*p)/(2*cosh(pi*p/2))
    amplitude_squared=6*bath.portal**2*h0*h0/k*form**2
    width=model.v_GeV*amplitude_squared/(2*q*sqrt(energy))
    return {'open':True,'width_GeV':width,'p':p,'form_factor':form,
            'imaginary_energy_over_v2':-amplitude_squared/(2*q),
            'scope':'Leading kappa^2 radiation width of the decoupled g=0 kink into a free radial Higgs channel. Background and channel distortions enter higher portal orders; finite Gaussian mixing is separate.'}


def reflection_amplitude(wall,energy,*,parity='opposite',radius=None,tol=1e-8,max_nodes=60000):
    """Unit incident amplitude on the single open asymptotic eigenchannel.

    Reference all phases to rho=0, not the arbitrary matching radius. The
    other two channels have decaying boundary conditions, retaining UV mixing.
    """
    energy=float(energy);radius=wall['L'] if radius is None else float(radius)
    thresholds,U=vacuum_channels(wall)
    if not np.isfinite(energy) or not thresholds[0]<energy<thresholds[1]:raise ValueError('exactly one open channel required')
    if parity not in ('opposite','translation') or not 0<radius<=wall['L'] or tol<=0:raise ValueError('resolved parity and radius required')
    opens=energy>thresholds;q=outgoing_wavenumbers(energy,thresholds,opens)
    K=U@np.diag(1j*q)@U.T
    incoming=U[:,0]*(-2j*q[0]*np.exp(-1j*q[0]*radius))
    grid=_mesh(wall,radius,energy)
    sign=1 if parity=='opposite' else -1
    waves=np.exp(-1j*q[0]*grid)+sign*np.exp(1j*q[0]*grid)
    derivative=-1j*q[0]*np.exp(-1j*q[0]*grid)+sign*1j*q[0]*np.exp(1j*q[0]*grid)
    guess=np.vstack((U[:,0,None]*waves,U[:,0,None]*derivative))
    def rhs(x,z):
        return np.vstack((z[3:],np.einsum('nij,jn->in',_potential(wall,x),z[:3])-energy*z[:3]))
    def jac(x,z):
        j=np.zeros((6,6,len(x)),complex);j[:3,3:]=np.eye(3)[:,:,None]
        j[3:,:3]=np.moveaxis(_potential(wall,x)-energy*np.eye(3),0,-1)
        return j
    def bc(a,b):
        left=np.r_[a[0],a[4],a[5]] if parity=='opposite' else np.r_[a[3],a[1],a[2]]
        return np.r_[left,b[3:]-K@b[:3]-incoming]
    def real_rhs(x,z):
        value=rhs(x,z[:6]+1j*z[6:]);return np.vstack((value.real,value.imag))
    def real_jac(x,z):
        a=jac(x,z);j=np.zeros((12,12,len(x)))
        j[:6,:6]=a.real;j[:6,6:]=-a.imag;j[6:,:6]=a.imag;j[6:,6:]=a.real
        return j
    def real_bc(a,b):
        value=bc(a[:6]+1j*a[6:],b[:6]+1j*b[6:]);return np.r_[value.real,value.imag]
    sol=solve_bvp(real_rhs,real_bc,grid,np.vstack((guess.real,guess.imag)),tol=tol,max_nodes=max_nodes,fun_jac=real_jac)
    if not sol.success:raise ArithmeticError(sol.message)
    final=sol.y[:6,-1]+1j*sol.y[6:,-1]
    amplitude=(U.T@final[:3])[0]*np.exp(-1j*q[0]*radius)-np.exp(-2j*q[0]*radius)
    return {'amplitude':[float(amplitude.real),float(amplitude.imag)],
            'flux_error':float(abs(abs(amplitude)**2-1)),
            'maximum_BVP_relative_residual':float(max(sol.rms_residuals)),
            'boundary_residual':float(max(abs(real_bc(sol.y[:,0],sol.y[:,-1])))),
            'radius_rho':radius,'parity':parity,'energy_over_v2':energy,'mesh_nodes':len(sol.x)}


def wall_scattering(wall,energy,**controls):
    """Reflection/transmission fluxes across the full reflection-symmetric wall."""
    even=reflection_amplitude(wall,energy,parity='opposite',**controls)
    odd=reflection_amplitude(wall,energy,parity='translation',**controls)
    plus=complex(*even['amplitude']);minus=complex(*odd['amplitude'])
    R=(plus+minus)/2;T=(plus-minus)/2
    return {'even_Higgs':even,'odd_Higgs':odd,
            'reflection_probability':float(abs(R)**2),'transmission_probability':float(abs(T)**2),
            'full_line_flux_error':float(abs(abs(R)**2+abs(T)**2-1)),
            'scope':'One open Higgs eigenchannel on both sides of the supplied reflection-symmetric wall. Parity reflection phases refer to the center. Finite-radius numerical scattering; not a network collision simulation.'}


def exact_shape_channel_conditions(model,bath):
    """Rational threshold and form-factor node tests on supplied decimal inputs."""
    from fractions import Fraction as Q
    l=Q(str(model.lam));h=Q(str(bath.v_GeV))/Q(str(model.v_GeV));H=Q(str(bath.lam))
    threshold=2*H*h*h;energy=3*l/2;node=threshold-l
    return {'shape_energy_over_v2':str(energy),'free_Higgs_threshold_over_v2':str(threshold),
            'channel_gap_over_v2':str(energy-threshold),'open':energy>threshold,
            'form_factor_node_polynomial':str(node),
            'leading_radiation_node':node==0,
            'node_relation':'2*lambda_H*(v_H/v)^2=lambda; p^2=1. Only the leading portal radiation amplitude vanishes, not the complete coupled width.'}
