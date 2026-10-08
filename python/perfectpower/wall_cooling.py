"""Thermal bulk ordering and canonical three-field static wall continuation.

Only declared leading quadratic thermal masses are included. No finite-T
collision kernel, gauge determinant, dynamical bath or interval BVP proof.
"""
from dataclasses import dataclass,asdict
from math import sqrt
import numpy as np
from scipy.integrate import solve_bvp,solve_ivp,quad
from scipy.optimize import brentq

@dataclass(frozen=True)
class CoolingInputs:
    v:float=30000.
    lam:float=1.76188164948e-5
    H:float=.13
    h0:float=.0082
    kappa:float=1e-7
    alpha:float=.1
    mu:float=10.
    c:float=.025
    cH:float=.4
    def __post_init__(self):
        if not all(np.isfinite(x) for x in asdict(self).values()):raise ValueError('finite inputs required')
        if min(self.v,self.lam,self.H,self.h0,self.mu,self.c,self.cH)<=0 or min(self.kappa,self.alpha)<0:raise ValueError('positive scales and nonnegative portals required')
        if self.c_eff<=0 or self.cH-self.kappa*self.c/self.le<=0:raise ValueError('ordered thermal branch slopes required')
    @property
    def le(self):return self.lam+self.kappa**2/self.H
    @property
    def c_eff(self):return self.c-self.kappa*self.cH/self.H
    @property
    def k0(self):return sqrt(self.le/2) # x=k0*v*z


def transitions(p=CoolingInputs()):
    A=1+p.kappa*p.h0**2/p.le
    slope=p.cH-p.kappa*p.c/p.le
    num=p.v**2*(p.H*p.h0**2-p.kappa*(A-1))
    bulk=sqrt(num/slope)
    cp=p.v*sqrt((p.le+p.kappa*p.h0**2)/p.c)
    nu=(sqrt(1+8*p.kappa/p.le)-1)/2
    # Exact analytic reduced-source kink and Higgs Pöschl-Teller ground state.
    wall=sqrt((num+p.le*p.v**2*A*nu**2/2)/(slope+p.c*nu**2/2))
    if not bulk<cp:raise ValueError('bulk Higgs transition must follow source ordering')
    return {'source_ordering_temperature_GeV':cp,'bulk_Higgs_ordering_temperature_GeV':bulk,
            'reduced_kink_wall_Higgs_onset_GeV':wall,'reduced_kink_wall_only_window_GeV':wall-bulk,
            'PT_exponent':nu,'thermal_mass_scope':'Declared polynomial mean-field thermal masses; not a gauge-resummed critical temperature.'}


def bulk_vacuum(T,p=CoolingInputs()):
    if not np.isfinite(T) or T<0:raise ValueError('finite nonnegative temperature required')
    tr=transitions(p);t2=(T/p.v)**2
    if T<tr['bulk_Higgs_ordering_temperature_GeV']:
        u2=1-p.c_eff*t2/p.lam
        h2=p.h0**2+p.kappa/p.H*(1-u2)-p.cH*t2/p.H
        phase='source_and_Higgs_broken'
    elif T<tr['source_ordering_temperature_GeV']:
        u2=(p.le+p.kappa*p.h0**2-p.c*t2)/p.le;h2=0.;phase='source_broken_Higgs_restored'
    else:u2=h2=0.;phase='both_restored'
    return {'u':sqrt(max(0.,u2)),'h':sqrt(max(0.,h2)),
            'y':-p.alpha*max(0.,u2)/p.mu**2,'phase':phase,
            'Higgs_curvature_GeV2':p.v**2*(p.H*(3*h2-p.h0**2)+p.kappa*(u2-1)+p.cH*t2)}


def excess_potential(u,y,h,T,p=CoolingInputs()):
    """Cancellation-free exact V(fields,T)-V(bulk,T), in units v^4."""
    b=bulk_vacuum(T,p);A=u*u-b['u']**2;B=h*h-b['h']**2
    rs=y+p.alpha*u*u/p.mu**2
    value=p.le*A*A/4+p.kappa*A*B/2+p.H*B*B/4+p.mu**2*rs*rs/2
    if b['h']==0:value+=b['Higgs_curvature_GeV2']/p.v**2*B/2
    # If both source and Higgs are restored the source KKT coefficient remains.
    if b['u']==0:value+=(p.c*(T/p.v)**2-p.le-p.kappa*p.h0**2)*u*u/2
    return value


def source_wall(T,p=CoolingInputs(),*,tol=2e-10,length=16.,nodes=400):
    b=bulk_vacuum(T,p)
    if b['h']!=0 or b['u']==0:raise ValueError('Higgs-restored source-broken bulk required')
    a=b['u'];L=length/a;x=np.linspace(0,L,nodes);u=a*np.tanh(a*x);du=a*a/np.cosh(a*x)**2
    y=-p.alpha*u*u/p.mu**2;dy=-2*p.alpha*u*du/p.mu**2
    def rhs(x,z):
        u,y,du,dy=z;rs=y+p.alpha*u*u/p.mu**2
        return np.array([du,dy,(p.le*u*(u*u-a*a)+2*p.alpha*u*rs)/p.k0**2,p.mu**2*rs/p.k0**2])
    def bc(left,right):return np.array([left[0],left[3],right[0]-a,right[1]-b['y']])
    sol=solve_bvp(rhs,bc,x,np.array([u,y,du,dy]),tol=tol,max_nodes=25000)
    if not sol.success:raise ArithmeticError(sol.message)
    return {'solution':sol,'L':L,'vacuum':b,'T':T,'p':p,'BVP_residual':float(max(sol.rms_residuals))}


def Higgs_zero_mode_match(T,p=CoolingInputs(),*,tol=2e-10,length=16.):
    """Even zero-mode logarithmic derivative at the wall center.

    Integrate inward from the decaying asymptotic condition; the finite wall
    tail is tested separately. This avoids guessing a Higgs-condensate amplitude.
    """
    w=source_wall(T,p,tol=tol,length=length);m2=w['vacuum']['Higgs_curvature_GeV2']/p.v**2/p.k0**2
    if m2<=0:raise ValueError('positive asymptotic Higgs mass needed')
    def rhs(x,r):
        u=w['solution'].sol(x)[0]
        return [m2+p.kappa/p.k0**2*(u*u-w['vacuum']['u']**2)-r[0]**2]
    sol=solve_ivp(rhs,(w['L'],0),[-sqrt(m2)],rtol=2e-11,atol=2e-13,max_step=.05)
    if not sol.success:raise ArithmeticError(sol.message)
    return float(sol.y[0,-1])


def full_wall_onset(p=CoolingInputs(),*,tol=2e-10,length=16.):
    tr=transitions(p);lo=tr['bulk_Higgs_ordering_temperature_GeV'];ref=tr['reduced_kink_wall_Higgs_onset_GeV']
    root=brentq(lambda T:Higgs_zero_mode_match(T,p,tol=tol,length=length),lo+1e-5,(ref-lo)*2+lo,xtol=2e-11)
    return {'temperature_GeV':root,'bulk_temperature_GeV':lo,'wall_only_window_GeV':root-lo,
            'reduced_reference_difference_GeV':root-ref,'center_log_derivative_residual':Higgs_zero_mode_match(root,p,tol=tol,length=length),
            'length_control':length,'BVP_tolerance':tol,'scope':'Canonical source/singlet BVP plus inward Riccati zero-mode shooting; numerical finite-tail threshold, not an interval enclosure.'}


def solve_thermal_wall(T,p=CoolingInputs(),*,tol=2e-9,length=14.,previous=None):
    b=bulk_vacuum(T,p)
    if b['u']==0:raise ValueError('no Z2 source wall above source ordering')
    a=b['u'];m2=b['Higgs_curvature_GeV2']/p.v**2/p.k0**2
    # Use an h=0 wall when its Higgs operator is stable. Below its localized
    # onset continue the positive condensate instead of the trivial branch.
    onset=transitions(p)['reduced_kink_wall_Higgs_onset_GeV']
    if b['h']==0 and T>onset+1e-5:
        w=source_wall(T,p,tol=tol,length=length)
        def evaluate(x):
            u,y,du,dy=w['solution'].sol(x);zero=np.zeros_like(u)
            return np.array([u,y,zero,du,dy,zero])
        L=w['L'];sol=None;res=w['BVP_residual']
    else:
        m=sqrt(max(m2,1e-7));L=max(length/a,length/m)
        core=min(16/a,L);x=np.unique(np.r_[np.linspace(0,core,450),np.geomspace(core,L,220)[1:] if L>core*(1+1e-12) else np.array([])])
        u=a*np.tanh(a*x);du=a*a/np.cosh(np.minimum(a*x,350))**2
        y=-p.alpha*u*u/p.mu**2;dy=-2*p.alpha*u*du/p.mu**2
        amp=max(b['h'],sqrt(max(p.kappa*a*a/p.H,1e-9)))
        h=b['h']+.25*amp*np.exp(-m*x);dh=-.25*amp*m*np.exp(-m*x)
        z=np.array([u,y,h,du,dy,dh])
        if previous is not None:
            z=previous['evaluate'](np.minimum(x,previous['L']))
            z[0]*=a/previous['vacuum']['u'];z[1]*=a*a/previous['vacuum']['u']**2
            z[2]=np.maximum(z[2],b['h'])
        def rhs(x,z):
            u,y,h,du,dy,dh=z;rs=y+p.alpha*u*u/p.mu**2;rh=h*h-p.h0**2+p.kappa/p.H*(u*u-1)
            return np.array([du,dy,dh,(p.lam*u*(u*u-1)+2*p.alpha*u*rs+p.kappa*u*rh+p.c*(T/p.v)**2*u)/p.k0**2,
                p.mu**2*rs/p.k0**2,(p.H*h*rh+p.cH*(T/p.v)**2*h)/p.k0**2])
        def bc(l,r):return np.array([l[0],l[4],l[5],r[0]-b['u'],r[1]-b['y'],r[2]-b['h']])
        sol=solve_bvp(rhs,bc,x,z,tol=tol,max_nodes=35000)
        if not sol.success:raise ArithmeticError(sol.message)
        evaluate=sol.sol;res=float(max(sol.rms_residuals))
        if T<onset-1e-4 and b['h']==0 and evaluate(0)[2]<1e-8:raise ArithmeticError('solver converged to trivial Higgs saddle')
    sample=np.unique(np.r_[np.linspace(0,min(16/a,L),401),np.geomspace(min(16/a,L),L,160)])
    z=evaluate(sample);V=excess_potential(*z[:3],T,p)
    kinetic=p.k0**2*np.sum(z[3:]**2,axis=0)/2
    def density(x):
        q=evaluate(x)
        return (p.k0**2*np.dot(q[3:],q[3:])/2+excess_potential(*q[:3],T,p))/p.k0
    core=min(16/a,L);pieces=[quad(density,lo,hi,epsabs=1e-14,epsrel=5e-10,limit=350) for lo,hi in [(0,core),(core,L)] if hi>lo]
    tension=2*sum(q[0] for q in pieces)*p.v**3
    higgs2_area=2*quad(lambda x:evaluate(x)[2]**2-b['h']**2,0,L,epsabs=1e-13,limit=350)[0]*p.v/p.k0
    report={'temperature_GeV':T,'bulk':b,'central_Higgs_GeV':float(z[2,0]*p.v),'tension_GeV3':tension,
        'quadrature_error_GeV3':2*sum(q[1] for q in pieces)*p.v**3,'BVP_residual':res,
        'first_integral_max_error_over_v4':float(np.max(abs(kinetic-V))),
        'Higgs_squared_excess_area_GeV':higgs2_area,'half_box_x':L,
        'profile':{'x':sample.tolist(),'source_GeV':(z[0]*p.v).tolist(),'singlet_GeV':(z[1]*p.v).tolist(),'Higgs_GeV':(z[2]*p.v).tolist()},
        'scope':'Canonical three-field finite-box numerical static wall for declared thermal mass potential; no full thermal effective action or damping.'}
    return {'evaluate':evaluate,'L':L,'vacuum':b,'report':report,'solution':sol}


def wall_condensation_energy(w,p=CoolingInputs(),*,tol=2e-10):
    """Paired energy difference from the h=0 canonical wall, avoiding huge tensions."""
    T=w['report']['temperature_GeV'];b=w['vacuum']
    if b['h']!=0:raise ValueError('wall-only condensate energy needs restored bulk')
    ref=source_wall(T,p,tol=tol,length=18)
    m2=b['Higgs_curvature_GeV2']/p.v**2
    def density(x):
        u,y,h,du,dy,dh=w['evaluate'](x)
        if x<=ref['L']:ur,yr,dur,dyr=ref['solution'].sol(x)
        else:ur,yr,dur,dyr=b['u'],b['y'],0.,0.
        # Remove the reference Euler-Lagrange linear variation before
        # evaluating: two ~1e11 GeV^3 tensions cannot resolve a tiny bifurcation.
        delta=u-ur;eta=y-yr;Rr=yr+p.alpha*ur*ur/p.mu**2
        Lr=eta+2*p.alpha*ur*delta/p.mu**2;Qr=p.alpha*delta*delta/p.mu**2
        V=p.le*(3*ur*ur-b['u']**2)*delta*delta/2+p.le*ur*delta**3+p.le*delta**4/4
        V+=p.alpha*Rr*delta*delta+p.mu**2*(Lr+Qr)**2/2
        V+=p.kappa*(u*u-b['u']**2)*h*h/2+p.H*h**4/4+m2*h*h/2
        K=p.k0**2*((du-dur)**2+(dy-dyr)**2+dh*dh)/2
        # Retain the actual spline's small E-L residual, so integration by
        # parts is an identity for this finite numerical reference as well.
        if x<=ref['L']:
            ddu,ddy=ref['solution'].sol(x,1)[2:]
            V+=(p.le*ur*(ur*ur-b['u']**2)+2*p.alpha*ur*Rr-p.k0**2*ddu)*delta
            V+=(p.mu**2*Rr-p.k0**2*ddy)*eta
        return (V+K)/p.k0
    boundaries=sorted(set([0.,min(ref['L'],w['L']),w['L']]))
    pieces=[quad(density,a,b,epsabs=1e-22,epsrel=2e-5,limit=350) for a,b in zip(boundaries[:-1],boundaries[1:])]
    end=min(ref['L'],w['L']);ur,yr,dur,dyr=ref['solution'].sol(end);u,y=w['evaluate'](end)[:2]
    boundary=p.k0*(dur*(u-ur)+dyr*(y-yr))
    return {'energy_difference_GeV3':2*p.v**3*(sum(x[0] for x in pieces)+boundary),'quadrature_error_GeV3':2*p.v**3*sum(x[1] for x in pieces),
        'definition':'sigma_positive_Higgs_wall - sigma_h_zero_wall at the same T; negative selects the condensate branch.',
        'scope':'Reference E-L linear variation removed, spline residual retained; paired numerical action difference, quadrature does not bound BVP error.'}


def projected_condensation(T,p=CoolingInputs()):
    """Leading one-mode Landau prediction around the exact reduced PT threshold."""
    from scipy.special import gammaln
    b=bulk_vacuum(T,p);nu=transitions(p)['PT_exponent'];k=p.v*p.k0*b['u']
    if nu<=0 or b['h']!=0 or k<=0:raise ValueError('positive portal and restored source-broken bulk needed')
    I2=np.exp(.5*np.log(np.pi)+gammaln(nu)-gammaln(nu+.5))/k
    I4=np.exp(.5*np.log(np.pi)+gammaln(2*nu)-gammaln(2*nu+.5))/k
    E0=b['Higgs_curvature_GeV2']-k*k*nu*nu
    amplitude=sqrt(max(0.,-E0*I2/(p.H*I4)))
    return {'PT_ground_eigenvalue_GeV2':E0,'predicted_central_Higgs_GeV':amplitude,
        'predicted_condensation_energy_GeV3':-min(E0,0.)**2*I2**2/(4*p.H*I4),
        'scope':'Leading near-onset one-mode projection; excludes source backreaction and heavy profile correction.'}


def gauge_background(report, *,g=.65,gY=.36):
    """Tree Higgs contribution to vector masses; no thermal Debye self-energy."""
    if min(g,gY)<0 or not np.isfinite(g+gY):raise ValueError('finite nonnegative gauge inputs required')
    h=np.asarray(report['profile']['Higgs_GeV'])
    return {'g':g,'gY':gY,'W_tree_mass_squared_GeV2':(g*g*h*h/4).tolist(),
        'Z_tree_mass_squared_GeV2':((g*g+gY*gY)*h*h/4).tolist(),
        'integrated_W_tree_mass_squared_defect_GeV':g*g*report['Higgs_squared_excess_area_GeV']/4,
        'integrated_Z_tree_mass_squared_defect_GeV':(g*g+gY*gY)*report['Higgs_squared_excess_area_GeV']/4,
        'scope':'Higgs background contribution only; thermal electric screening, magnetic sector and damping are not computed.'}


def robin_defect_condensation(T,p=CoolingInputs()):
    """Spectrally matched thin-wall Robin model; no fitted parameter.

    q=k*nu matches the exact reduced kink's linear binding. The nonlinear
    half-line tail is solved exactly; finite-width backreaction remains out.
    """
    b=bulk_vacuum(T,p)
    if b['h']!=0 or b['u']==0:raise ValueError('restored source-broken bulk required')
    q=p.v*p.k0*b['u']*transitions(p)['PT_exponent'];m=sqrt(b['Higgs_curvature_GeV2'])
    amp=sqrt(max(0.,2*(q*q-m*m)/p.H))
    energy=-2*(q-m)**2*(q+2*m)/(3*p.H) if q>m else 0.
    return {'matched_Robin_q_GeV':q,'asymptotic_Higgs_mass_GeV':m,
        'predicted_central_Higgs_GeV':amp,'predicted_condensation_energy_GeV3':energy,
        'scope':'Exact nonlinear Robin-defect tail with q matched to the reduced-kink linear binding; finite-width approximation, not the canonical wall.'}


def cubic_background(report,p=CoolingInputs(), *,full_profile=False):
    """Canonical third derivatives in GeV on the numerical thermal background.

    Vertices are local potential tensors, not mode overlaps or decay widths.
    G denotes one Cartesian Higgs angular component in the O(4) potential.
    """
    u=np.asarray(report['profile']['source_GeV'])/p.v;h=np.asarray(report['profile']['Higgs_GeV'])/p.v
    arrays={'phi_phi_phi':p.v*(6*p.le*u+12*p.alpha**2*u/p.mu**2),
        'phi_phi_S':np.full_like(u,2*p.alpha*p.v),'phi_phi_h':2*p.kappa*p.v*h,
        'phi_h_h':2*p.kappa*p.v*u,'h_h_h':6*p.H*p.v*h,'h_G_G':2*p.H*p.v*h}
    result={k:a.tolist() if full_profile else float(a[0]) for k,a in arrays.items()}
    return {'vertices_GeV':result,'full_profile':full_profile,'scope':'Local tree third derivatives only; no normalized mode projections, widths, bath collisions or loop corrections.'}
