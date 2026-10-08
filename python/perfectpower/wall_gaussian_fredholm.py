"""Gaussian-coupled leading radiation node and its first portal correction.

All background and shape data retain finite mediator gradients. The threshold
and portal correction are derived from real cosine solvability conditions,
not fitted nonlinear quartics or outgoing widths. Finite-radius evidence only.
"""
from dataclasses import replace
from math import sqrt
import numpy as np
from scipy.integrate import solve_bvp,quad
from scipy.optimize import brentq
from .wall_fluctuations import HiggsWall,solve_coupled_wall


def gaussian_node_response(model, *, h0=1., length=32., tol=1e-10):
    if model.bias_h0_GeV3 or not np.isfinite(h0) or h0<=0:
        raise ValueError('unbiased static action and positive finite Higgs ratio required')
    if not np.isfinite(length) or length<20 or not np.isfinite(tol) or not 0<tol<1e-3:
        raise ValueError('finite resolved domain and positive tight tolerance required')
    k=sqrt(model.lam/2);alpha=model.current_g_GeV/model.v_GeV;mu=model.heavy_mass_GeV/model.v_GeV
    bath=HiggsWall(portal=0.,lam=model.lam/(2*h0*h0),v_GeV=h0*model.v_GeV)
    wall=solve_coupled_wall(model,bath,length_factor=length,tol=tol,central_nodes=900)
    R=k*wall['L'];grid=np.linspace(0,R,900)
    def background(x):return wall['solution'].sol(np.asarray(x)/k)
    def matrix(x):
        u,y=background(x)[:2];rs=y+alpha*u*u/mu**2
        M=np.zeros((len(np.atleast_1d(x)),2,2))
        M[:,0,0]=(model.lam*(3*u*u-1)+2*alpha*rs+4*alpha*alpha*u*u/mu**2)/k**2
        M[:,0,1]=M[:,1,0]=2*alpha*u/k**2;M[:,1,1]=mu**2/k**2
        return M
    vacuum=np.array([[2*model.lam+4*alpha*alpha/mu**2,2*alpha],[2*alpha,mu**2]])/k**2
    thresholds,U=np.linalg.eigh(vacuum)
    if thresholds[0]<=3*.7:raise ValueError('reference shape outside resolved closed-source continuation')
    def mode_rhs(x,z,e):return np.vstack((z[2:],np.einsum('nij,jn->in',matrix(x),z[:2])-e[0]*z[:2]))
    def mode_bc(a,b,e):
        decay=(U*np.sqrt(thresholds-e[0]))@U.T
        return np.r_[a[0],a[3],a[2]-1,b[2:]+decay@b[:2]]
    u=np.tanh(grid);s=1/np.cosh(grid);p=s*u;dp=s*(1-2*u*u)
    r=-2*alpha*u*p/mu**2;dr=-2*alpha*(s*s*p+u*dp)/mu**2
    shape=solve_bvp(mode_rhs,mode_bc,grid,np.array([p,r,dp,dr]),p=[min(3.,.85*thresholds[0])],tol=tol,max_nodes=30000)
    if not shape.success:raise ArithmeticError('closed source shape: '+shape.message)
    E=float(shape.p[0])
    if not 0<E<thresholds[0]:raise ArithmeticError('shape not below coupled source continuum')
    def source(x):return background(x)[0]*shape.sol(x)[0]
    def integral(f):return 2*quad(f,0,R,epsabs=2e-11,epsrel=2e-11,limit=300)[0]
    def form_factor(q):return integral(lambda x:np.cos(q*x)*source(x))
    qs=np.linspace(.15*sqrt(E),.95*sqrt(E),28);fs=[form_factor(q) for q in qs]
    brackets=[(a,b) for a,b,fa,fb in zip(qs[:-1],qs[1:],fs[:-1],fs[1:]) if fa*fb<0]
    if not brackets:raise ArithmeticError('no leading radiation zero in the scanned open-channel interval')
    bracket=min(brackets,key=lambda pair:abs((pair[0]+pair[1])/2-1))
    q_moment=brentq(form_factor,*bracket,xtol=1e-13)
    def g_rhs(x,z,q2):return np.array([z[1],-q2[0]*z[0]+2*source(x)])
    def open_bc(a,b,param):return np.array([a[1],b[0],b[1]])
    G=solve_bvp(g_rhs,open_bc,grid,np.array([s,-s*u]),p=[q_moment*q_moment],tol=tol,max_nodes=30000)
    if not G.success:raise ArithmeticError('leading open response: '+G.message)
    q=sqrt(float(G.p[0]));m=E-q*q
    if m<=0:raise ArithmeticError('nonpositive tuned Higgs threshold')
    H=solve_bvp(lambda x,z:np.array([z[1],m*z[0]-(1-background(x)[0]**2)]),
        lambda a,b:np.array([a[1],b[1]+sqrt(m)*b[0]]),grid,np.zeros((2,len(grid))),tol=tol,max_nodes=30000)
    if not H.success:raise ArithmeticError('static Higgs response: '+H.message)
    def force(x):
        u=background(x)[0];p=shape.sol(x)[0];h=H.sol(x)[0]
        return 2*u*h*p+(3*m*h+u*u-1)*G.sol(x)[0]
    B=solve_bvp(lambda x,z,C:np.array([z[1],-q*q*z[0]+force(x)+C[0]*G.sol(x)[0]]),
        open_bc,grid,np.zeros((2,len(grid))),p=[-1.36],tol=tol,max_nodes=30000)
    if not B.success:raise ArithmeticError('next open response: '+B.message)
    denominator=integral(lambda x:np.cos(q*x)*G.sol(x)[0])
    fprime=integral(lambda x:-x*np.sin(q*x)*source(x))
    if abs(denominator)<1e-6:raise ArithmeticError('degenerate radiation node')
    C_overlap=-integral(lambda x:np.cos(q*x)*force(x))/denominator
    C=float(B.p[0]);sample=np.linspace(0,min(20,R),401)
    return {'source_lambda':model.lam,'alpha':alpha,'mu':mu,'h0':h0,'k':k,
        'shape_energy_over_v2':E*k*k,'shape_energy_over_k2':E,
        'source_thresholds_over_v2':(thresholds*k*k).tolist(),
        'leading_node_threshold_over_v2':m*k*k,'leading_node_threshold_over_k2':m,
        'leading_node_shift_from_scalar_threshold':m*k*k-model.lam,
        'open_wave_number_over_k':q,'independent_form_factor_root_over_k':q_moment,
        'linear_threshold_coefficient':C,'independent_cosine_linear_coefficient':C_overlap,
        'radiation_transversality_moment':denominator,'independent_transversality_from_form_factor':-fprime/q,
        'leading_form_factor_at_node':form_factor(q),'scalar_node_form_factor':form_factor(sqrt(max(E-2,1e-15))),
        'scanned_radiation_roots':len(brackets),'radius_x':R,'tol':tol,
        'maximum_residuals':{'background':wall['report']['maximum_BVP_relative_residual'],
            'shape':float(max(shape.rms_residuals)),'G':float(max(G.rms_residuals)),
            'H':float(max(H.rms_residuals)),'B':float(max(B.rms_residuals))},
        'shape_boundary_residual':float(max(abs(mode_bc(shape.y[:,0],shape.y[:,-1],shape.p)))),
        'profile':{'x':sample.tolist(),'u':background(sample)[0].tolist(),'S':background(sample)[1].tolist(),
            'source_shape':shape.sol(sample)[0].tolist(),'singlet_shape':shape.sol(sample)[1].tolist(),
            'G':G.sol(sample)[0].tolist(),'H':H.sol(sample)[0].tolist(),'B':B.sol(sample)[0].tolist()},
        'solutions':{'background':wall['solution'],'shape':shape,'G':G,'H':H,'B':B},
        'scope':'Exact Gaussian action retained in finite-radius numerical source wall/shape and linear portal responses. One selected leading node and nonzero cosine transversality; no infinite-domain existence, uniqueness of every radiation zero or quantum protection.'}


def fixed_Higgs_source_prediction(model,bath,*,length=32.,tol=1e-10):
    """Invert the derived leading-plus-linear node, holding Higgs inputs fixed."""
    h0=bath.v_GeV/model.v_GeV;target=2*bath.lam*h0*h0
    cache={}
    def evaluate(lam):
        if lam not in cache:cache[lam]=gaussian_node_response(replace(model,lam=lam),h0=h0,length=length,tol=tol)
        return cache[lam]
    def equation(lam):
        r=evaluate(lam)
        return r['leading_node_threshold_over_v2']+r['linear_threshold_coefficient']*bath.portal-target
    lam=brentq(equation,target*.6,target*1.6,xtol=target*1e-11)
    r=evaluate(lam)
    return {'predicted_source_lambda':lam,'fixed_Higgs_lambda':bath.lam,'target_threshold_over_v2':target,
        'portal':bath.portal,'leading_node_threshold_over_v2':r['leading_node_threshold_over_v2'],
        'linear_threshold_coefficient':r['linear_threshold_coefficient'],
        'source_lambda_equation_residual':equation(lam),'response_evaluations':len(cache),
        'scope':'Source-quartic inversion of the derived coupled node through first portal order, not a fit to the full localized candidate. Quadratic portal correction remains uncomputed for nonzero Gaussian coupling.'}


def singlet_resolvent_check(response, *, points=(0.,.25,.8,1.5,3.)):
    """Independent heavy Green convolution, scaled to resolve narrow kernels."""
    k=response['k'];alpha=response['alpha'];mu=response['mu'];R=response['radius_x']
    beta=sqrt(mu*mu/(k*k)-response['shape_energy_over_k2'])
    wall=response['solutions']['background'];shape=response['solutions']['shape']
    def f(x):return wall.sol(x/k)[0]*shape.sol(x)[0]
    def q(fun,upper):
        return quad(fun,0,min(upper,50.),epsabs=1e-12,epsrel=1e-12,limit=200)[0] if upper>0 else 0.
    checks=[]
    for x in points:
        if not np.isfinite(x) or not 0<=x<R:raise ValueError('finite interior convolution points required')
        left=q(lambda t:np.exp(-t)*f(x-t/beta),beta*x)
        right=q(lambda t:np.exp(-t)*f(x+t/beta),beta*(R-x))
        reflected=np.exp(-beta*x)*q(lambda t:np.exp(-t)*f(t/beta),beta*R)
        predicted=-alpha*(left+right+reflected)/(k*k*beta*beta)
        actual=float(shape.sol(x)[1])
        checks.append({'x':x,'mode_from_BVP':actual,'mode_from_heavy_Green_kernel':predicted,
                       'absolute_difference':abs(actual-predicted)})
    return {'points':checks,'maximum_absolute_difference':max(t['absolute_difference'] for t in checks),
        'kernel_decay_over_x':beta,'kernel_exponential_cutoff':50,
        'scope':'Independent even heavy-channel Green convolution on the finite source profile. No certified tail enclosure.'}


def exact_gaussian_portal_identities():
    """Exact portal bookkeeping with the finite Gaussian square retained."""
    import sympy as sp
    q=sp.Symbol('kappa')
    u,y,h0,h1,H0,L1,lam,alpha,mu,P,S,Q1,Q2,E=sp.symbols('u y h0 h1 H0 L1 lambda alpha mu P S Q1 Q2 E')
    h=h0+q*h1;H=H0+q*L1
    V=lam*(u*u-1)**2/4+mu*mu*(y+alpha*u*u/mu**2)**2/2+H*(h*h-h0*h0+q/H*(u*u-1))**2/4
    # Differentiate in independent canonical fields before the series pullback.
    U,Y,Z=sp.symbols('U Y Z')
    independent=lam*(U*U-1)**2/4+mu*mu*(Y+alpha*U*U/mu**2)**2/2+H*(Z*Z-h0*h0+q/H*(U*U-1))**2/4
    pull={U:u,Y:y,Z:h}
    coefficient=lambda expr,n:sp.expand(sp.series(expr,q,0,n+1).removeO()).coeff(q,n)
    fu=sp.diff(independent,U).subs(pull);fy=sp.diff(independent,Y).subs(pull);fh=sp.diff(independent,Z).subs(pull)
    hh=sp.diff(independent,Z,2).subs(pull);uh=sp.diff(independent,U,Z).subs(pull);yh=sp.diff(independent,Y,Z).subs(pull)
    mode=uh*P+yh*S+(hh-E)*(q*Q1+q*q*Q2)
    checks={'source_first_portal_force_zero':coefficient(fu,1),
        'heavy_first_portal_force_zero':coefficient(fy,1),
        'static_Higgs_response':coefficient(fh,1)-(2*H0*h0*h0*h1+h0*(u*u-1)),
        'direct_heavy_Higgs_Hessian_zero':yh,
        'leading_open_force':coefficient(mode,1)-((2*H0*h0*h0-E)*Q1+2*u*h0*P),
        'next_open_force':coefficient(mode,2)-((2*H0*h0*h0-E)*Q2+2*u*h1*P+(6*H0*h0*h1+2*L1*h0*h0+u*u-1)*Q1)}
    t,w,fp=sp.symbols('t w Fprime',nonzero=True)
    checks['Fourier_transversality_limit']=sp.limit(2*fp*t/(w*w-(w+t)**2),t,0)+fp/w
    reduced={n:sp.factor(v) for n,v in checks.items()}
    if any(v!=0 for v in reduced.values()):raise ArithmeticError('coupled polynomial coefficient mismatch')
    return {n:str(v) for n,v in reduced.items()}
