"""Complete one-dimensional logarithmic-quartic geometry and radial profiling.

Analytic classification uses the two real Lambert W branches. Numerical values
use arbitrary-precision function evaluation; this is not interval arithmetic.
"""
from dataclasses import dataclass
import math
import mpmath as mp
import numpy as np


@dataclass(frozen=True)
class LogQuartic:
    scale_squared: float
    strength: float
    control: object

    def __post_init__(self):
        if not all(math.isfinite(x) and x>0 for x in [self.scale_squared,self.strength]):
            raise ValueError('Finite positive logarithmic scale and strength required')
        if isinstance(self.control,str):
            if self.control not in ['fold','coexistence','origin']:raise ValueError('Unknown exact phase boundary')
        elif not math.isfinite(self.control):raise ValueError('Finite control required')

    def eta(self):
        if self.control=='fold':return -1/mp.e
        if self.control=='coexistence':return -1/(2*mp.sqrt(mp.e))
        if self.control=='origin':return mp.mpf(0)
        return mp.mpf(self.control)

    def evaluate(self,h):
        if not math.isfinite(h):raise ValueError('Finite radial coordinate required')
        with mp.workdps(60):
            s=mp.mpf(self.scale_squared);d=mp.mpf(self.strength);eta=self.eta();x=mp.mpf(h);y=x*x/s
            if h==0:return 0.,0.,float(-d*s*eta)
            L=mp.log(y)
            return tuple(float(v) for v in [d*s*s*(y*y*(L-mp.mpf('.5'))-2*eta*y)/4,
                d*x*s*(y*L-eta),d*s*(y*(3*L+2)-eta)])

    def classify(self):
        with mp.workdps(60):
            eta=self.eta();fold=-1/mp.e;coex=-1/(2*mp.sqrt(mp.e))
            phase=('origin_only' if eta<fold else 'fold' if eta==fold else
                'broken_metastable' if eta<coex else 'coexistence' if eta==coex else
                'origin_metastable' if eta<0 else 'origin_spinodal' if eta==0 else 'broken_only')
            points=[{'h':0.,'y':0.,'branch':'origin','energy':0.,'curvature':float(-self.strength*self.scale_squared*eta),
                'type':'minimum' if eta<0 else 'degenerate_unstable' if eta==0 else 'maximum'}]
            if eta>=fold:
                branches=[('fold',mp.mpf(-1))] if eta==fold else [('W0',mp.re(mp.lambertw(eta,0)))]+([('W-1',mp.re(mp.lambertw(eta,-1)))] if eta<0 else [])
                for branch,w in branches:
                    y=mp.exp(w);h=mp.sqrt(self.scale_squared*y)
                    energy=-mp.mpf(self.strength)*mp.mpf(self.scale_squared)**2*y*(eta+y/2)/4
                    if self.control=='coexistence' and branch=='W0':energy=mp.mpf(0)
                    k=2*mp.mpf(self.strength)*self.scale_squared*y*(1+w)
                    for sign in [-1,1]:points.append({'h':float(sign*h),'y':float(y),'branch':branch,'energy':float(energy),'curvature':float(k),
                        'type':'fold' if branch=='fold' else 'maximum' if branch=='W-1' else 'minimum'})
            if phase in ['origin_only','fold','broken_metastable']:ground=[0.]
            elif phase=='coexistence':ground=[p['h'] for p in points if p['type']=='minimum']
            else:ground=[p['h'] for p in points if p['branch']=='W0']
            maxima=[p for p in points if p['branch']=='W-1' and p['h']>0];minima=[p for p in points if p['branch']=='W0' and p['h']>0]
            barrier={} if not maxima else {'from_origin':maxima[0]['energy'],'from_broken_minimum':maxima[0]['energy']-minima[0]['energy']}
            return {'phase':phase,'control':float(eta),'stationary_points':points,'global_radial_minima':ground,'barriers':barrier,
                'scope':'Complete global classification of this one-dimensional potential only. Critical string inputs denote exact analytic thresholds; ordinary float controls retain their supplied value.'}

    def minimum_positive_radius(self):
        p=next((p for p in self.classify()['stationary_points'] if p['branch']=='W0' and p['h']>0),None)
        if p is None:raise ValueError('No nondegenerate positive broken minimum')
        return p['h']

    def control_response(self):
        h=self.minimum_positive_radius();y=h*h/self.scale_squared;w=math.log(y)
        return {'dy_deta':1/(1+w),'dh_deta':math.sqrt(self.scale_squared)/(2*math.sqrt(y)*(1+w)),
                'd_minimum_energy_deta':-self.strength*self.scale_squared**2*y/2,
                'd2_minimum_energy_deta2':-self.strength*self.scale_squared**2/(2*(1+w))}


def compile_vector_radial(model,X,r=1e-6,g=.65,gprime=.36,mu=1.,reference_h=None):
    """Compile the full fixed-other-coordinate tree slice plus calibrated W/Z.

    Neutral scalar/quark determinants are a separate remainder. Coefficients
    follow directly from the Higgs portals and quadratic mediator currents.
    """
    from .flavor_gauge_feedback import pulled_vector_CW
    X=np.asarray(X,float);h0=model.vac[20] if reference_h is None else reference_h
    if not np.all(np.isfinite(X)) or h0<=0:raise ValueError('Finite background and positive reference radius required')
    pulled_vector_CW(h0,r,g,gprime,mu)
    a=np.array([g*g/4,(g*g+gprime*gprime)/4]);n=np.array([6.,3.]);active=a>0;a=a[active];n=n[active]
    if not len(a):raise ValueError('A nonzero vector logarithmic coefficient is required')
    C=n*a*a/(64*np.pi**2*r);d=4*sum(C);L0=np.log(a*h0*h0/(r*mu**2));delta=4*h0*h0*sum(C*(L0-1/3))
    z0=X[:21].copy();z0[20]=0.;J0,_=model.current(z0)
    e=np.zeros(21);e[20]=1.;_,D=model.current(e);ch=D[:,20]
    q,_=model.invariants(z0);F0=X[21:]+J0/model.M**2;t=X[-1]-model.vac[-1]
    B=-model.mu2+model.portals@q[:8]+ch@F0+t*t*model.k[-1]/2
    lam=.13+(ch@ch)/(2*model.M**2)
    alpha=lam+4*sum(C*(L0-1/3));squared=h0*h0*math.exp(-alpha/d)
    eta=-(B-delta)/(d*squared)
    potential=LogQuartic(squared,d,eta)
    return potential,{'tree_quadratic_coefficient':float(B),'tree_quartic_coefficient':float(lam),
        'finite_Higgs_mass_adjustment':float(delta),'normal_scale_squared':squared,'normal_strength':float(d),'normal_control':float(eta),
        'scope':'Exact analytic tree-plus-vector radial slice at fixed remaining 48 coordinates. Other loop determinants are excluded from this compiler.'}


def profile_hessian(H,radial_index=20):
    """Exact Schur complement and inertia boundary, without inverse formation."""
    H=np.asarray(H,float)
    if H.ndim!=2 or H.shape[0]!=H.shape[1] or not np.all(np.isfinite(H)) or np.max(abs(H-H.T))>1e-9:
        raise ValueError('Finite real symmetric Hessian required')
    if not 0<=radial_index<len(H):raise ValueError('Valid radial index required')
    indices=[j for j in range(len(H)) if j!=radial_index];c=H[radial_index,radial_index]
    if c<=0:raise ValueError('Positive nonzero radial curvature required for minimum profiling')
    b=H[indices,radial_index];A=H[np.ix_(indices,indices)];S=A-np.outer(b,b)/c
    return S,-b/c


def profiled_hard_branch(model,r=1e-6,g=.65,gprime=.36,mu=1.):
    """A 48-coordinate solve with analytic radial seeding and loop refinement.

    This solves the same explicitly calibrated truncated potential as the
    full 49-coordinate routine; no new electroweak inputs are introduced.
    """
    from .flavor_gauge_feedback import calibrated_vector_CW
    if not 0<r<=1e-6:raise ValueError('Declared local weak-point range required')
    X=model.vac.copy();h0=X[20];indices=[i for i in range(len(X)) if i!=20];history=[]
    def F(Y):
        f=model.potential(Y)[1]+r*model.loop_gradient(Y,mu)
        f[20]+=calibrated_vector_CW(Y[20],h0,r,g,gprime,mu)[1];return f
    for iteration in range(8):
        normal,coefficients=compile_vector_radial(model,X,r,g,gprime,mu,h0);seed=normal.minimum_positive_radius();X[20]=seed
        for radial_iteration in range(8):
            f=F(X)
            if abs(f[20])<1e-13:break
            curvature=model.full_hessian(X)[20,20]+calibrated_vector_CW(X[20],h0,r,g,gprime,mu)[2]
            X[20]-=f[20]/curvature
        else:raise RuntimeError('Radial loop remainder did not converge')
        H=model.full_hessian(X)+r*model.loop_hessian(X,mu);H[20,20]+=calibrated_vector_CW(X[20],h0,r,g,gprime,mu)[2]
        H=(H+H.T)/2;S,response=profile_hessian(H);residual=float(np.max(abs(f)))
        history.append({'iteration':iteration,'maximum_tadpole_residual':residual,'radial_remainder_updates':radial_iteration,
            'Lambert_seed_minus_final_radius':float(seed-X[20]),'radial_normal_phase':normal.classify()['phase']})
        if residual<2e-14:break
        X[indices]-=np.linalg.solve(S,f[indices])
    else:raise RuntimeError('Profiled 48-coordinate solve did not converge')
    return {'r':r,'rescaled_coordinates_Y':X.tolist(),'iteration_history':history,'maximum_tadpole_residual':residual,
        'minimum_profiled_48_curvature_eigenvalue':float(np.linalg.eigvalsh(S)[0]),
        'minimum_full_49_curvature_eigenvalue':float(np.linalg.eigvalsh(H)[0]),'radial_curvature':float(H[20,20]),
        'radial_response_norm':float(np.linalg.norm(response)),
        'scope':'Exact radial tree-plus-vector seeding plus numerical neutral/quark loop refinement of the previously specified finite-Higgs-mass-calibrated hard potential. Local response, not a global 49-field minimum, dressed pole spectrum or golden relation.'}


def exact_radial_identities():
    import sympy as s
    y,eta=s.symbols('y eta',positive=True);u=(y*y*(s.log(y)-s.Rational(1,2))-2*eta*y)/4
    assert s.simplify(s.diff(u,y)-(y*s.log(y)-eta)/2)==0
    assert s.simplify(u.subs(eta,y*s.log(y))+y*(y*s.log(y)+y/2)/4)==0
    co=s.exp(-s.Rational(1,2));assert s.simplify(u.subs({y:co,eta:-co/2}))==0
    assert s.simplify(s.diff(y*s.log(y),y).subs(y,s.exp(-1)))==0
    b,c,k=s.symbols('b c k',positive=True);assert s.simplify(b*b/c-b*b/(c+k)-b*b*k/(c*(c+k)))==0
    return {'normal_form':'V(h)=d s^4 [y^2(log y-1/2)-2 eta y]/4; y=h^2/s^2',
        'stationary_equation':'y log y = eta; y=exp(W0(eta)) or exp(W-1(eta))',
        'fold':'eta=-1/e; y=1/e','coexistence':'eta=-1/(2 sqrt(e)); y=1/sqrt(e)',
        'origin_spinodal':'eta=0','universal_coexistence_to_fold_control_ratio':'sqrt(e)/2',
        'stationary_energy':'-d s^4 y(eta+y/2)/4','stationary_radial_curvature':'2 d s^2 y[1+W(eta)]',
        'profile_curvature':'A-b b^T/c','positive_radial_stiffening':'S(c+k)-S(c)=k b b^T/[c(c+k)] is positive semidefinite for c>0,k>=0',
        'inertia':'inertia(H)=inertia(c)+inertia(A-b b^T/c)',
        'fold_response':'dy/deta=1/[1+W0(eta)], divergent at the broken-branch fold',
        'coexistence_suppression':'No gauge-independent physical phase-transition claim follows from this conditional radial classification.'}
