"""Two-bulk-particle emission from a canonically normalized planar wall mode.

Normal momentum is not conserved. Standing parity waves have full-line
normalization int dz f_k f_l=delta(k-l), k,l>0. Physical TE vector widths
include one polarization only; ungauged Goldstones are a separate theory.
"""
from math import pi, sqrt
import numpy as np
from scipy.integrate import solve_ivp, simpson
from scipy.interpolate import CubicSpline, RectBivariateSpline
from numpy.polynomial.legendre import leggauss


def parity_continuum(x, potential, momenta, *, rtol=2e-10):
    """Solve (-d_x^2+U)f=q^2 f, U vanishing at the matching endpoint.

    momenta are positive dimensionless q=k_z/(v*k_wall). The normalization
    is in physical normal momentum; no additional sqrt(v*k_wall) occurs.
    """
    x=np.asarray(x,float);q=np.asarray(momenta,float);U=np.asarray(potential,float)
    if x.ndim!=1 or len(x)<4 or x[0]!=0 or np.any(np.diff(x)<=0):raise ValueError('increasing half-line mesh starting at zero required')
    if U.shape!=x.shape or q.ndim!=1 or len(q)<1 or np.any(q<=0) or not np.all(np.isfinite(q)):raise ValueError('finite positive normal momenta and matching potential required')
    if not np.all(np.isfinite(U)) or rtol<=0:raise ValueError('finite potential and positive tolerance required')
    n=len(q);ui=CubicSpline(x,U)
    # Layout parity, value/derivative, momentum. Odd derivative is q, which
    # avoids a 1/q-sized solution in the low-energy free limit.
    initial=np.zeros((2,2,n));initial[0,0]=1;initial[1,1]=q
    def rhs(t,z):
        z=z.reshape(2,2,n);out=np.empty_like(z);out[:,0]=z[:,1];out[:,1]=(ui(t)-q*q)*z[:,0]
        return out.ravel()
    sol=solve_ivp(rhs,(0,x[-1]),initial.ravel(),t_eval=x,method='DOP853',rtol=rtol,atol=rtol*.05)
    if not sol.success:raise ArithmeticError(sol.message)
    z=sol.y.reshape(2,2,n,len(x));amplitude=np.hypot(z[:,0,:,-1],z[:,1,:,-1]/q)
    waves=z[:,0]/amplitude[:,:,None]/sqrt(pi)
    return {'waves':waves,'endpoint_potential':float(U[-1]),'asymptotic_amplitudes':amplitude,
            'endpoint_unit_amplitude_error':float(np.max(abs(pi*(waves[:,:,-1]**2+(z[:,1,:,-1]/amplitude/q)**2/pi)-1)))}


def pair_phase_space(mass, bulk_mass, order=64):
    """Nested Gauss rule on sqrt(k^2+m^2)+sqrt(l^2+m^2)<M."""
    if not np.isfinite(mass) or mass<=0 or not np.isfinite(bulk_mass) or bulk_mass<0 or order<4:raise ValueError('positive parent mass, nonnegative bulk mass, order>=4 required')
    if mass<=2*bulk_mass:return np.empty((0,0)),np.empty((0,0)),np.empty((0,0))
    a,w=leggauss(order);a=(a+1)/2;w=w/2
    maximum=sqrt(mass*(mass-2*bulk_mass));k=maximum*a
    lm=np.sqrt(np.maximum((mass-np.sqrt(k*k+bulk_mass**2))**2-bulk_mass**2,0))
    return np.broadcast_to(k[:,None],(order,order)),lm[:,None]*a,maximum*w[:,None]*lm[:,None]*w


def continuum_pair_width(mass, bulk_mass, momenta, overlaps, *, identical=True, species=1, order=64, temperature=0.):
    """Gamma=S*n/(8 M^2) int dk dl sum_parity |G_ab(k,l)|^2.

    Even vertices admit ee and oo only. G has units GeV^(1/2). The exact
    transverse-momentum integration is 1/(4M); identical-particle S=1/2.
    """
    if not np.isfinite(temperature) or temperature<0:raise ValueError('nonnegative finite bath temperature required')
    k,l,w=pair_phase_space(mass,bulk_mass,order)
    if not k.size:return {'width_GeV':0.,'even_even_GeV':0.,'odd_odd_GeV':0.,'open':False}
    nodes=np.asarray(momenta,float);G=np.asarray(overlaps,float)
    if len(nodes)<4 or np.any(np.diff(nodes)<=0) or G.shape!=(2,len(nodes),len(nodes)) or species<=0:raise ValueError('ordered overlap grid, two same-parity kernels and positive multiplicity required')
    if k.min()<nodes[0] or l.min()<nodes[0] or k.max()>nodes[-1] or l.max()>nodes[-1]:raise ValueError('phase space outside supplied continuum grid')
    factor=species*(.5 if identical else 1)/(8*mass*mass)
    if temperature>0:
        omega1=(mass*mass+k*k-l*l)/(2*mass);omega2=mass-omega1
        # Retarded damping: decay minus inverse decay, not emission alone.
        with np.errstate(over='ignore'):
            w=w*(1+1/np.expm1(omega1/temperature)+1/np.expm1(omega2/temperature))
    values=[]
    for kernel in G:
        f=RectBivariateSpline(nodes,nodes,kernel,kx=3,ky=3,s=0)
        values.append(float(factor*np.sum(w*f.ev(k.ravel(),l.ravel()).reshape(k.shape)**2)))
    return {'width_GeV':sum(values),'even_even_GeV':values[0],'odd_odd_GeV':values[1],'open':True}


def candidate_pair_data(solution, *, channel='global_Goldstone', g=.4, gprime=.36,
                        momentum_nodes=193, spatial_nodes=2601, rtol=2e-10, order=64):
    """On-shell distorted-wave Born width; retains the full wall profile."""
    wall=solution['wall'];model=wall['model'];bath=wall['bath'];scale=model.v_GeV*wall['k']
    x=np.linspace(0,wall['k']*wall['L'],spatial_nodes);rho=x/wall['k']
    u,y,h=wall['solution'].sol(rho)[:3];psi=solution['mode'].sol(x)[:3]/wall['k']
    norm=2*simpson(np.sum(psi*psi,axis=0),x=rho);normalization=sqrt(model.v_GeV/norm)
    M=model.v_GeV*sqrt(solution['mode_energy_over_v2']);h0=bath.v_GeV/model.v_GeV
    if channel=='global_Goldstone':
        m=0.;U=(bath.lam*(h*h-h0*h0)+bath.portal*(u*u-1))/wall['k']**2
        vertex=normalization*(2*bath.portal*u*psi[0]+2*bath.lam*h*psi[2]);identical=True;species=3
    elif channel in ('W_TE','Z_TE'):
        if min(g,gprime)<=0:raise ValueError('positive declared gauge couplings required')
        coupling=g*g if channel=='W_TE' else g*g+gprime*gprime
        m=sqrt(coupling)*bath.v_GeV/2
        U=coupling*(h*h-h0*h0)/(4*wall['k']**2)
        vertex=normalization*coupling*h*psi[2]/2;identical=channel=='Z_TE';species=1
    else:raise ValueError('resolved Goldstone or physical TE vector channel required')
    if M<=2*m:return {'channel':channel,'mass_GeV':M,'bulk_mass_GeV':m,'width_GeV':0.,'open':False}
    k,l,_=pair_phase_space(M,m,order)
    minimum=min(k.min(),l.min())*.2;maximum=sqrt(M*(M-2*m))*1.00001
    # Cluster near zero: the vector barrier produces a narrow threshold layer.
    grid=minimum+(maximum-minimum)*np.linspace(0,1,momentum_nodes)**2
    continuum=parity_continuum(x,U,grid/scale,rtol=rtol)
    waves=continuum['waves']
    if spatial_nodes%2!=1:raise ValueError('odd spatial node count required for Simpson quadrature')
    weights=np.ones(spatial_nodes);weights[1:-1:2]=4;weights[2:-1:2]=2
    weights*= (x[1]-x[0])/3
    # Full-line integral: 2 dx/(v*k_wall) times physical cubic v^(3/2)/sqrt(N).
    # vertex was sqrt(v/N)*dimensionless cubic, leaving 2/k_wall dx.
    kernels=np.array([2/wall['k']*(f*(vertex*weights)[None,:])@f.T for f in waves])
    result=continuum_pair_width(M,m,grid,kernels,identical=identical,species=species,order=order)
    return {**result,'channel':channel,'mass_GeV':M,'bulk_mass_GeV':m,
        'lifetime_seconds_in_this_channel':6.582119569e-25/result['width_GeV'] if result['width_GeV']>0 else None,
        'momentum_nodes':momentum_nodes,'spatial_nodes':spatial_nodes,'phase_space_order':order,
        'normalization_over_rho':norm,'endpoint_potential_over_wall_scale2':continuum['endpoint_potential'],
        'endpoint_unit_amplitude_error':continuum['endpoint_unit_amplitude_error'],
        'scope':'Three physical global Goldstones in the ungauged O(4) theory.' if channel=='global_Goldstone' else
        'One physical polarization perpendicular to both the wall normal and parallel outgoing momentum. Partial WW/ZZ width, not the full vector width.',
        'normal_momentum_GeV':grid.tolist(),'overlap_even_even_GeV_half':kernels[0].tolist(),
        'overlap_odd_odd_GeV_half':kernels[1].tolist()}
