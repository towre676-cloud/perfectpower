"""Universal Fredholm responses for the decoupled-singlet scalar wall.

Derives the quadratic node correction from linear forced equations, without
fitting either a nonlinear candidate curve or outgoing radiation widths.
Decimals and response solves are numerical, not certified error enclosures.
"""
from math import pi, cosh, sqrt
import numpy as np
from scipy.integrate import solve_bvp, quad


def universal_responses(*, radius_x=32., tol=1e-11):
    """Solve five universal response equations and their solvability moments.

    u=tanh(x), s=sech(x), p=s*u. H and T are even static Higgs
    responses, A the odd static source response, B the even open-channel
    second mode response, W the normalized odd source-mode response.
    """
    if not np.isfinite(radius_x) or radius_x < 16 or not np.isfinite(tol) or not 0 < tol < 1e-3:
        raise ValueError('finite resolved radius and positive tight tolerance required')
    x = np.linspace(0, radius_x, 600)
    solutions = {}
    def solve(name, rhs, bc, *, parameters=None):
        sol = solve_bvp(rhs, bc, x, np.zeros((2, len(x))), p=parameters,
                        tol=tol, max_nodes=30000)
        if not sol.success:
            raise ArithmeticError(name + ': ' + sol.message)
        solutions[name] = sol
        return sol
    H = solve('H', lambda x,z: np.array([z[1],2*z[0]-1/np.cosh(x)**2]),
              lambda a,b: np.array([a[1],b[1]+sqrt(2)*b[0]]))
    def forcing_B(x):
        s=1/np.cosh(x)
        return s*((8-2*s*s)*H.sol(x)[0]-s*s)
    B = solve('B', lambda x,z,c: np.array([z[1],-z[0]+forcing_B(x)+c[0]/np.cosh(x)]),
              lambda a,b,c: np.array([a[1],b[0],b[1]]), parameters=np.array([-1.36]))
    C=float(B.p[0]);F=pi/cosh(pi/2)
    A = solve('A', lambda x,z: np.array([z[1],(4-6/np.cosh(x)**2)*z[0]
                  +np.tanh(x)*(2*H.sol(x)[0]-1/np.cosh(x)**2)]),
              lambda a,b: np.array([a[0],b[0]]))
    T = solve('T', lambda x,z: np.array([z[1],2*z[0]+3*H.sol(x)[0]**2
                  +C*H.sol(x)[0]-H.sol(x)[0]/np.cosh(x)**2]),
              lambda a,b: np.array([a[1],b[1]+sqrt(2)*b[0]]))
    def w_rhs(x,z,e):
        s=1/np.cosh(x);u=np.tanh(x);p=s*u
        a2=12*u*A.sol(x)[0]+2*H.sol(x)[0]+3*u*u-1
        return np.array([z[1],(1-6*s*s)*z[0]+(a2-e[0])*p+2*u*s])
    pR=float(np.tanh(radius_x)/np.cosh(radius_x))
    W = solve('W',w_rhs,lambda a,b,e: np.array([a[0],a[1],b[1]+b[0]+(4-e[0])*pR/2]),
              parameters=np.array([3.]))
    e=float(W.p[0])
    def even_integral(f):
        value,err=quad(f,0,radius_x,epsabs=1e-11,epsrel=1e-11,limit=300)
        return 2*value,2*err
    c_overlap,cerr=even_integral(lambda q: np.cos(q)*forcing_B(q))
    def moments(q):
        u=np.tanh(q);s=1/np.cosh(q);p=s*u
        h=H.sol(q)[0];t=T.sol(q)[0];a=A.sol(q)[0];b=B.sol(q)[0];w=W.sol(q)[0]
        higgs=2*u*t*p+(6*h+C-s*s)*b+s*(6*t+3*h*h+3*C*h)
        source=2*u*w+2*a*p-e*s
        return higgs,source
    ia,ea=even_integral(lambda q: np.cos(q)*moments(q)[0])
    ib,eb=even_integral(lambda q: np.cos(q)*moments(q)[1])
    numerator,enerr=even_integral(lambda q: (np.tanh(q)/np.cosh(q))**2*(
        12*np.tanh(q)*A.sol(q)[0]+2*H.sol(q)[0]+3*np.tanh(q)**2+1))
    denominator=2/3
    return {'linear_threshold_coefficient':C,'quadratic_Higgs_coefficient':-ia/F,
            'quadratic_source_coefficient':-ib/F,'shape_energy_coefficient':e,
            'independent_cosine_linear_coefficient':-c_overlap/F,
            'independent_Fredholm_energy_coefficient':numerator/denominator,
            'quadrature_error_estimates':{'linear':cerr/F,'Higgs':ea/F,'source':eb/F,'energy':enerr/denominator},
            'maximum_response_residuals':{name:float(max(sol.rms_residuals)) for name,sol in solutions.items()},
            'boundary_residuals':{'H':float(abs(H.y[1,0])), 'A':float(abs(A.y[0,0])),
                'B_even':float(abs(B.y[1,0])),'B_exterior':float(max(abs(B.y[:,-1]))),
                'T':float(abs(T.y[1,0])),'W_value':float(abs(W.y[0,0])),'W_normalization':float(abs(W.y[1,0]))},
            'radius_x':radius_x,'tol':tol,'solutions':solutions,
            'scope':'g=0, fixed positive source quartic and h0. Universal linear-response hierarchy, numerical coefficients; no certified asymptotic remainder or infinite-domain existence theorem.'}


def retuning_coefficients(source_lambda, h0, *, responses=None, radius_x=32., tol=1e-11):
    """Unmixed threshold = lambda + C*kappa + Q*kappa^2 + O(kappa^3)."""
    if not np.isfinite(source_lambda) or source_lambda<=0 or not np.isfinite(h0) or h0<=0:
        raise ValueError('finite positive source quartic and Higgs vacuum ratio required')
    r=universal_responses(radius_x=radius_x,tol=tol) if responses is None else responses
    quadratic=2/source_lambda*(r['quadratic_Higgs_coefficient']+h0*h0*r['quadratic_source_coefficient'])
    return {'linear_threshold_coefficient':r['linear_threshold_coefficient'],
            'quadratic_threshold_coefficient':float(quadratic),
            'quadratic_shape_energy_coefficient':float(2*h0*h0/source_lambda*r['shape_energy_coefficient']),
            'source_lambda':source_lambda,'h0':h0,'scope':r['scope']}


def threshold_series(kappa, source_lambda, h0, *, responses=None):
    if not np.isfinite(kappa):raise ValueError('finite portal required')
    c=retuning_coefficients(source_lambda,h0,responses=responses)
    c['threshold_through_quadratic']=source_lambda+c['linear_threshold_coefficient']*kappa+c['quadratic_threshold_coefficient']*kappa*kappa
    c['Higgs_lambda_through_quadratic']=c['threshold_through_quadratic']/(2*h0*h0)
    c['shape_energy_through_quadratic']=1.5*source_lambda+c['quadratic_shape_energy_coefficient']*kappa*kappa
    return c


def exact_hierarchy_identities():
    """Exact rational-symbolic coefficient extraction from the square action.

    This checks algebra over rational functions, not differential existence or
    floating-point profiles. The O(kappa^3) diagonal portal term cannot enter
    the O(kappa^3) Higgs forcing because that mode begins at O(kappa).
    """
    import sympy as sp
    q=sp.Symbol('kappa')
    U,U2,h0,h1,h2,P,P2,Q1,Q2,Q3,lam,H0,L1,L2,E0,E2=sp.symbols(
        'U U2 h0 h1 h2 P P2 Q1 Q2 Q3 lambda H0 L1 L2 E0 E2')
    u=U+q*q*U2;h=h0+q*h1+q*q*h2
    psi=P+q*q*P2;chi=q*Q1+q*q*Q2+q**3*Q3
    H=H0+q*L1+q*q*L2;E=E0+q*q*E2
    inverse_H=1/H0-q*L1/H0**2+q*q*(L1**2/H0**3-L2/H0**2)
    fu=lam*u*(u*u-1)+q*u*(h*h-h0*h0)+q*q*inverse_H*u*(u*u-1)
    fh=H*h*(h*h-h0*h0)+q*h*(u*u-1)
    aa=lam*(3*u*u-1)+q*(h*h-h0*h0)+q*q*inverse_H*(3*u*u-1)
    bb=2*q*u*h;dd=H*(3*h*h-h0*h0)+q*(u*u-1)
    fpsi=(aa-E)*psi+bb*chi;fchi=bb*psi+(dd-E)*chi
    A0=lam*(3*U*U-1);A2=6*lam*U*U2+2*h0*h1+(3*U*U-1)/H0
    D1=6*H0*h0*h1+2*L1*h0*h0+U*U-1
    D2=6*H0*h0*h2+3*H0*h1*h1+6*L1*h0*h1+2*L2*h0*h0
    def coefficient(expr,n):return sp.expand(expr).coeff(q,n)
    checks={
        'static_source_order_1_zero':coefficient(fu,1),
        'static_source_order_2':coefficient(fu,2)-(A0*U2+2*h0*U*h1+U*(U*U-1)/H0),
        'static_Higgs_order_1':coefficient(fh,1)-(2*H0*h0*h0*h1+h0*(U*U-1)),
        'static_Higgs_order_2':coefficient(fh,2)-(2*H0*h0*h0*h2+3*H0*h0*h1*h1+2*L1*h0*h0*h1+h1*(U*U-1)),
        'source_mode_order_1_zero':coefficient(fpsi,1),
        'source_mode_order_2':coefficient(fpsi,2)-((A0-E0)*P2+(A2-E2)*P+2*U*h0*Q1),
        'Higgs_mode_order_1':coefficient(fchi,1)-((2*H0*h0*h0-E0)*Q1+2*U*h0*P),
        'Higgs_mode_order_2':coefficient(fchi,2)-((2*H0*h0*h0-E0)*Q2+2*U*h1*P+D1*Q1),
        'Higgs_mode_order_3':coefficient(fchi,3)-((2*H0*h0*h0-E0)*Q3+2*U*h0*P2+2*(U*h2+U2*h0)*P+D1*Q2+(D2-E2)*Q1),
        'source_background_absent_from_Higgs_diagonal_order_2':sp.diff(coefficient(dd,2),U2),
        'shape_norm':sp.integrate(sp.Symbol('t')**2,(sp.Symbol('t'),-1,1))-sp.Rational(2,3)}
    k,Hr,Tr,Ar,Br,Wr,C,er,sech,t=sp.symbols('k H T A B W C e s t', nonzero=True)
    subs={lam:2*k*k,H0:k*k/h0**2,L1:C/(2*h0**2),
          h1:h0*Hr/k**2,h2:h0*Tr/k**4,U2:h0**2*Ar/k**4,
          P:sech*U/k,P2:h0**2*Wr/k**5,Q1:h0*sech/k**3,
          Q2:h0*Br/k**5,E2:h0**2*er/k**2,L2:0}
    third=2*U*h0*P2+2*(U*h2+U2*h0)*P+D1*Q2+(D2-E2)*Q1
    scaled=h0/k**5*(2*U*Tr*sech*U+(6*Hr+C+U*U-1)*Br
         +sech*(6*Tr+3*Hr*Hr+3*C*Hr)
         +h0*h0*(2*U*Wr+2*Ar*sech*U-er*sech))
    checks['universal_third_force_parameter_separation']=sp.expand(third.subs(subs,simultaneous=True)-scaled)
    def derivative(poly):return sech**2*sp.diff(poly,t)-sech*t*sp.diff(poly,sech)
    norm_relation=t*t+sech*sech-1
    checks['scalar_wall_equation']=derivative(derivative(t))+2*t*sech*sech
    checks['odd_shape_equation']=sp.rem(sp.expand(derivative(derivative(sech*t))-(1-6*sech*sech)*sech*t),norm_relation,t)
    checks['leading_localized_open_response']=sp.rem(sp.expand(derivative(derivative(sech))+sech-2*t*sech*t),norm_relation,t)
    reduced={name:sp.factor(expr) for name,expr in checks.items()}
    if any(value!=0 for value in reduced.values()):raise ArithmeticError('symbolic hierarchy mismatch')
    return {name:str(value) for name,value in reduced.items()}
