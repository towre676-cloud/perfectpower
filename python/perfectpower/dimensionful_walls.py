"""Dimensionful Gaussian walls and explicitly conditional radiation-era screens.

GeV, GeV^3 and GeV^4 are the energy, tension and bias units. The thermal
potential and bias history are model inputs. Network and GW parameters are
phenomenological inputs, not outputs of the static wall boundary problem.
"""
from dataclasses import dataclass,asdict
from fractions import Fraction as Q
from math import pi,sqrt
import numpy as np
from scipy.integrate import solve_bvp,quad
from scipy.optimize import brentq

MPL_REDUCED_GEV=2.435e18
HBAR_GEV_S=6.582119569e-25
T0_GEV=2.34865418e-13
GSTAR0=3.36
GSTAR_S0=3.91
OMEGA_RAD_H2=4.18e-5


@dataclass(frozen=True)
class WallModel:
    v_GeV:float
    lam:float
    thermal_c:float
    heavy_mass_GeV:float
    current_g_GeV:float
    bias_h0_GeV3:float=0.
    bias_onset_GeV:float=0.

    def __post_init__(self):
        if not all(np.isfinite(x) for x in asdict(self).values()):raise ValueError('finite physical inputs required')
        if min(self.v_GeV,self.lam,self.thermal_c,self.heavy_mass_GeV)<=0 or min(self.current_g_GeV,self.bias_h0_GeV3,self.bias_onset_GeV)<0:raise ValueError('positive scales and nonnegative couplings/bias required')
        if self.bias_h0_GeV3 and not 0<self.bias_onset_GeV<self.critical_temperature_GeV:raise ValueError('declared late bias onset must be below the unbiased critical temperature')

    @property
    def critical_temperature_GeV(self):return self.v_GeV*sqrt(self.lam/self.thermal_c)

    def h(self,T):
        if T<0:raise ValueError('nonnegative temperature required')
        return self.bias_h0_GeV3*max(0.,1-(T/self.bias_onset_GeV)**2) if self.bias_onset_GeV else 0.


def tension_bounds(model):
    """Rigorous unbiased zero-temperature sandwich using a lifted source kink.

    Every full path costs at least the projected source kink. Lifting the
    exact source kink to S=-g phi^2/M^2 adds a computable heavy kinetic cost.
    """
    v,lam,M,g=model.v_GeV,model.lam,model.heavy_mass_GeV,model.current_g_GeV
    lower=2*sqrt(2*lam)*v**3/3
    ratio=Q(2,5)*Q(str(g))**2*Q(str(v))**2/Q(str(M))**4
    return {'lower_GeV3':lower,'upper_GeV3':lower*(1+float(ratio)),
            'exact_trial_relative_excess':str(ratio),
            'scope':'Unbiased canonical Gaussian UV wall: sigma_source <= sigma_UV <= sigma_source*(1+2*g^2*v^2/(5*M^4)). The tiny late bias is treated separately, not as a static degenerate wall.'}


def solve_wall(model,*,length_factor=18.,tol=1e-8,nodes=700):
    lam=model.lam;mu=model.heavy_mass_GeV/model.v_GeV;alpha=model.current_g_GeV/model.v_GeV
    k=sqrt(lam/2);L=length_factor/k;rho=np.linspace(-L,L,nodes)
    u=np.tanh(k*rho);du=k*(1-u*u);y=-alpha*u*u/mu**2;dy=-2*alpha*u*du/mu**2
    def equations(r,z):
        u,y,p,q=z;valley=y+alpha*u*u/mu**2
        return np.array([p,q,lam*u*(u*u-1)+2*alpha*u*valley,mu**2*valley])
    def boundaries(a,b):return np.array([a[0]+1,b[0]-1,a[1]+alpha/mu**2,b[1]+alpha/mu**2])
    sol=solve_bvp(equations,boundaries,rho,np.array([u,y,du,dy]),tol=tol,max_nodes=30000)
    if not sol.success:raise ArithmeticError(sol.message)
    def density(r):
        u,y,p,q=sol.sol(r);V=lam*(u*u-1)**2/4+mu**2*(y+alpha*u*u/mu**2)**2/2
        return (p*p+q*q)/2+V
    action,error=quad(density,-L,L,epsabs=2e-12,epsrel=2e-11,limit=300)
    sample=np.linspace(-L,L,401);u,y,p,q=sol.sol(sample)
    V=lam*(u*u-1)**2/4+mu**2*(y+alpha*u*u/mu**2)**2/2
    bounds=tension_bounds(model);sigma=action*model.v_GeV**3
    return {'tension_GeV3':sigma,'dimensionless_tension':action,'quadrature_error_GeV3':error*model.v_GeV**3,
            'analytic_bounds':bounds,'boundary_residual':float(max(abs(boundaries(sol.y[:,0],sol.y[:,-1])))),
            'maximum_BVP_relative_residual':float(max(sol.rms_residuals)),
            'first_integral_maximum_error':float(max(abs((p*p+q*q)/2-V))),
            'profile':{'rho':sample.tolist(),'phi_over_v':u.tolist(),'S_over_v':y.tolist()},
            'scope':'Numerical two-field static unbiased wall; analytic sandwich is exact, solver is not a certified differential-equation integrator.'}


def thermal_vacua(model,T,*,digits=80):
    """High-precision cubic stationary points avoid subtracting huge energies."""
    import mpmath as mp
    if T<0:raise ValueError('nonnegative temperature required')
    with mp.workdps(digits):
        v,lam,c,temp,h=map(lambda x:mp.mpf(str(x)),[model.v_GeV,model.lam,model.thermal_c,T,model.h(T)])
        a=lam*v*v-c*temp*temp
        discriminant=4*a**3-27*lam*h*h
        if a>0 and discriminant>0:
            radius=mp.sqrt(a/lam)
            roots=[mp.findroot(lambda x:lam*x**3-a*x-h,start) for start in [-radius,mp.mpf(0),radius]]
        else:
            roots=[mp.findroot(lambda x:lam*x**3-a*x-h,max(v,h**(mp.mpf(1)/3)))] if h else [mp.mpf(0)]
        rows=[]
        for x in sorted(roots):
            value=lam*(x*x-v*v)**2/4+c*temp*temp*x*x/2-h*x
            rows.append({'phi_GeV':mp.nstr(x,50),'energy_GeV4':mp.nstr(value,50),
                         'source_curvature_GeV2':mp.nstr(3*lam*x*x-a,50),
                         'stationarity_residual':mp.nstr(lam*x**3-a*x-h,8)})
        minima=[(x,lam*(x*x-v*v)**2/4+c*temp*temp*x*x/2-h*x) for x in roots if 3*lam*x*x-a>0]
        gap=max(e for x,e in minima)-min(e for x,e in minima) if len(minima)==2 else mp.mpf(0)
        return {'temperature_GeV':T,'stationary_points':rows,'two_local_minima':len(minima)==2,
                'exact_numeric_energy_gap_GeV4':mp.nstr(gap,50),'precision_digits':digits,
                'cubic_discriminant':mp.nstr(discriminant,30)}


def radiation_H(T,gstar,*,planck=MPL_REDUCED_GEV):
    if T<=0 or gstar<=0 or planck<=0:raise ValueError('positive radiation inputs required')
    return sqrt(pi*pi*gstar/90)*T*T/planck


def radiation_T(H,gstar):
    if H<=0 or gstar<=0:raise ValueError('positive H and radiation degrees required')
    return sqrt(H*MPL_REDUCED_GEV/sqrt(pi*pi*gstar/90))


def Higgs_bath_completion(model,*,portal=1e-7,higgs_lam=.13,higgs_v_GeV=246.,thermal_higgs_c=.4):
    """A concrete CP-even decay channel, with a positive-square static completion.

    Add lambda_H/4 [2 H^dagger H-v_H^2+(kappa/lambda_H)(phi^2-v^2)]^2.
    Holding H at its vacuum in the lifted source-kink trial adds the displayed
    potential cost. Width is leading phi->hh, neglecting tiny scalar mixing.
    """
    if min(portal,higgs_lam,higgs_v_GeV,thermal_higgs_c)<0 or min(higgs_lam,higgs_v_GeV,thermal_higgs_c)==0:raise ValueError('nonnegative portal and positive Higgs inputs required')
    m=sqrt(2*model.lam)*model.v_GeV;mh=sqrt(2*higgs_lam)*higgs_v_GeV
    width=portal**2*model.v_GeV**2/(8*pi*m)*sqrt(max(0.,1-4*mh*mh/(m*m)))
    cost=Q(str(portal))**2/(2*Q(str(higgs_lam))*Q(str(model.lam)))
    original=tension_bounds(model)
    Tc=sqrt((model.lam*model.v_GeV**2+portal*higgs_v_GeV**2+portal**2*model.v_GeV**2/higgs_lam)/model.thermal_c)
    return {'portal_kappa':portal,'Higgs_lambda':higgs_lam,'Higgs_v_GeV':higgs_v_GeV,
            'source_mass_GeV':m,'Higgs_mass_GeV':mh,'leading_phi_to_hh_width_GeV':width,
            'lifetime_seconds':HBAR_GEV_S/width if width else None,
            'exact_source_kink_relative_potential_cost':str(cost),
            'three_field_tension_bounds_GeV3':[original['lower_GeV3'],original['upper_GeV3']+original['lower_GeV3']*float(cost)],
            'thermal_portal_mass_coefficient':portal/3,
            'declared_Higgs_thermal_c':thermal_higgs_c,
            'leading_three_field_CP_transition_GeV':Tc,
            'Higgs_curvature_at_CP_transition_GeV2':thermal_higgs_c*Tc*Tc-higgs_lam*higgs_v_GeV**2-portal*model.v_GeV**2,
            'low_temperature_source_thermal_c_after_Higgs_minimization':model.thermal_c-portal*thermal_higgs_c/higgs_lam,
            'static_completion':'V_Gaussian + lambda_H/4*[2 HdaggerH-v_H^2+(kappa/lambda_H)*(phi^2-v^2)]^2. All squares vanish at phi=+-v, S=-g*v^2/M^2, 2 HdaggerH=v_H^2.',
            'scope':'Explicit spectator Higgs-bath example, not the nonet quark matching. Leading decay width and mean-field thermal coefficients with +c_H*T^2*(2 HdaggerH)/2. Full gauge-resummed thermal effective action and relic Boltzmann history are not computed.'}


def annihilation(model,sigma,*,area=.8,annihilation_factor=3.,gstar=10.75):
    if min(sigma,area,annihilation_factor,gstar,model.bias_h0_GeV3)<=0:raise ValueError('positive wall/network/bias inputs required')
    Tc=model.critical_temperature_GeV
    def gap(T):return 2*model.h(T)*model.v_GeV*sqrt(max(0.,1-(T/Tc)**2))
    def balance(T):return 2*annihilation_factor*area*sigma*radiation_H(T,gstar)-gap(T)
    hi=min(Tc,model.bias_onset_GeV)*(1-1e-8)
    T=brentq(balance,1e-10,hi,xtol=1e-14,rtol=1e-12);H=radiation_H(T,gstar)
    return {'temperature_GeV':T,'H_GeV':H,'time_seconds':HBAR_GEV_S/(2*H),
            'bias_gap_GeV4':gap(T),'wall_fraction':2*area*sigma/(3*MPL_REDUCED_GEV**2*H),
            'convention':'rho_wall=A*sigma/t=2*A*sigma*H; t_ann=C_ann*A*sigma/DeltaV in radiation domination.',
            'scope':'Classical scaling balance with a first-order tiny-bias gap; network formation and annihilation are not simulated.'}


def spectrum_shape(ratio,*,middle_break=10.,middle_slope=-1.,uv_slope=-1.):
    x=np.asarray(ratio,float)
    if np.any(x<=0) or middle_break<1 or middle_slope>=0 or uv_slope>=0:raise ValueError('positive frequencies and decaying UV slopes required')
    return np.where(x<=1,x**3,np.where(x<=middle_break,x**middle_slope,middle_break**middle_slope*(x/middle_break)**uv_slope))


def gw_estimate(sigma,H_ann,*,area=.8,efficiency=.7,gstar=10.75,gstar_s=10.75,
                emission_H_ratio=1.,peak_frequency_in_H=1.,middle_break=10.,middle_slope=-1.,uv_slope=-1.,frequencies=None,
                wall_inverse_width_GeV=None):
    if min(sigma,H_ann,area,efficiency,gstar,gstar_s,emission_H_ratio,peak_frequency_in_H)<=0 or emission_H_ratio>1:raise ValueError('positive GW inputs and emission ratio <=1 required')
    H=emission_H_ratio*H_ann;T=radiation_T(H,gstar)
    redshift=T0_GEV/T*(GSTAR_S0/gstar_s)**(1/3)
    # f_em=peak_frequency_in_H*H in the chosen literature cyclic-frequency
    # convention. Equivalently k_em=2*pi*peak_frequency_in_H*H.
    peak=peak_frequency_in_H*H/HBAR_GEV_S*redshift
    omega_em=efficiency*area*area*sigma*sigma/(24*pi*MPL_REDUCED_GEV**4*H*H)
    dilution=OMEGA_RAD_H2*(gstar/GSTAR0)*(GSTAR_S0/gstar_s)**(4/3)
    amplitude=dilution*omega_em
    if frequencies is None:frequencies=np.logspace(-12,-3,361)
    frequencies=np.asarray(frequencies,float)
    shape=spectrum_shape(frequencies/peak,middle_break=middle_break,middle_slope=middle_slope,uv_slope=uv_slope)
    # Integral over all logarithmic frequencies of the stipulated template.
    integral=1/3+(middle_break**middle_slope-1)/middle_slope-middle_break**middle_slope/uv_slope
    result={'emission_H_ratio':emission_H_ratio,'emission_temperature_GeV':T,
            'peak_frequency_Hz':peak,'peak_Omega_h2':amplitude,'integrated_Omega_h2':amplitude*integral,
            'hypothetical_scaling_wall_fraction_at_emission':2*area*sigma/(3*MPL_REDUCED_GEV**2*H),
            'frequency_Hz':frequencies.tolist(),'Omega_h2':(amplitude*shape).tolist(),
            'shape_inputs':{'middle_break':middle_break,'middle_slope':middle_slope,'uv_slope':uv_slope,'IR_slope':3},
            'scope':'Input-calibrated radiation-era quadrupole/redshift template. Delayed-emission cases are sensitivity scenarios, not lattice predictions for this potential.'}
    if wall_inverse_width_GeV is not None:
        if wall_inverse_width_GeV<=0:raise ValueError('positive inverse wall width required')
        cutoff=wall_inverse_width_GeV/HBAR_GEV_S*redshift
        if cutoff<=peak:raise ValueError('thin wall cutoff must exceed the peak')
        result['wall_width_cutoff_frequency_Hz']=cutoff
        result['integrated_flat_UV_cap_Omega_h2']=amplitude*(1/3+float(np.log(cutoff/peak))+1)
        result['flat_UV_cap_assumptions']='IR f^3 below peak; amplitude never exceeds the declared peak up to the wall-width cutoff; at most one peak unit of integrated exponentially suppressed tail above cutoff. A spectral envelope assumption, not a simulation bound.'
    return result
