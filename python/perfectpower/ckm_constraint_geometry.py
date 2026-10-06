"""Observable polynomial CKM constraints and their conditional elliptic slice.

The input is a unitary three-family frame. Finite vectorlike light currents
must first be divided by their calculated doublet weights. Target equations
describe a constraint locus; they do not supply its protecting interaction.
"""
import numpy as np
from fractions import Fraction as Q


def constraint_data(a,b,c,d,J):
    t=1-c;K=a*b*c*(t-a)*(t-b);N=a*b+c*(t-a)*(t-b)-d*t*t
    golden=c*c*t**4-7*a*b*c*t*t+a*a*b*b
    phase=N**8-7*N**6*K+14*N**4*K*K-8*N*N*K**3+K**4
    return {'t':t,'K':K,'N':N,'unitary_CP_polynomial':4*t*t*J*J+N*N-4*K,
            'golden_polynomial':golden,'phase_carrier_polynomial':phase,
            'small_golden_branch':bool(a>0 and b>0 and 0<c*t*t<a*b),
            'positive_66_branch':bool(K>0 and N>0 and J>0 and Q(16,25)*K<N*N<Q(1681,2500)*K)}


def frame_constraints(V,atol=1e-9):
    V=np.asarray(V,complex)
    if V.shape!=(3,3) or np.max(abs(V@V.conj().T-np.eye(3)))>atol:
        raise ValueError('Unitary three-family frame required')
    a,b,c,d=[float(abs(V[i,j])**2) for i,j in [(0,1),(1,2),(0,2),(2,0)]]
    J=float(np.imag(V[0,1]*V[1,2]*V[0,2].conjugate()*V[1,1].conjugate()))
    r=constraint_data(a,b,c,d,J);K,N=r['K'],r['N'];t=1-c
    r.update({'squared_magnitudes':[a,b,c,d],'J':J,
              'depth':float(np.sqrt(c)*t/np.sqrt(a*b)) if a*b else None,
              'cos_standard_phase':float(N/(2*np.sqrt(K))) if K>0 else None,
              'unitarity_polynomial_scaled_residual':float(r['unitary_CP_polynomial']/max(K,1e-300)),
              'golden_scaled_residual':float(r['golden_polynomial']/max((a*b)**2,1e-300)),
              'phase_scaled_residual':float(r['phase_carrier_polynomial']/max(K**4,1e-300))})
    return r


def elliptic_slice(c,X):
    """Fixed |Vub|^2=c and depth^2=X, with an independently fixed phase.

    x=a/(1-c), b=c(1-c)/(X x). The equation is
    (x J)^2=k c sin(delta)^2 x(1-x)(x-c/X).
    Return its phase-free cubic up to a nonzero quadratic twist.
    """
    c,X=Q(c),Q(X)
    if not 0<c<1 or X<=0 or c==X:
        raise ValueError('Nonsingular slice with 0<c<1 and X>0, c!=X required')
    lam=c/X;t=1-c;k=c*t*t/X
    return {'lambda':str(lam),'k':str(k),'cubic_constant_first':['0',str(-lam),str(1+lam),'-1'],
            'discriminant':str(lam*lam*(1-lam)**2),'genus':1,
            'j_invariant':str(256*(1-lam+lam*lam)**3/(lam*lam*(1-lam)**2)),
            'physical_interval':{'lower':str(lam),'upper':'1'} if lam<1 else None,
            'scope':'Conditional fixed-magnitude/phase target slice; no point is selected by this geometry.'}


def exact_geometry_certificate():
    import sympy as s
    a,b,c,x,X=s.symbols('a b c x X');t=1-c;k=c*t*t/X
    K=a*b*c*(t-a)*(t-b)
    assert s.cancel(K.subs({a:t*x,b:k/(t*x)})-k*c*t*t*(1-x)*(x-c/X)/x)==0
    f=x*(1-x)*(x-c/X)
    assert s.factor(s.discriminant(f,x)-c*c*(X-c)**2/X**4)==0
    z=s.symbols('z');P=x**8-7*x**6+14*x**4-8*x*x+1
    assert s.expand(z**8*P.subs(x,z+1/z)-s.cyclotomic_poly(60,z))==0
    assert s.Poly(P,x).count_roots(s.Rational(4,5),s.Rational(41,50))==1
    from .rational_functions import RationalFunction as RF,AlgebraBudget
    from .symmetry_quotients import PolynomialCurve
    from .differential_extensions import matrix_encode
    budget=AlgebraBudget();lam=RF([0,1],budget=budget);zero=lam.coerce(0)
    curve=PolynomialCurve([zero,-lam,1+lam,lam.coerce(-1)],budget)
    return {'elliptic_slice_identity':True,'elliptic_discriminant_identity':True,
            'phase_minimal_polynomial':str(P),'positive_66_isolating_interval':['4/5','41/50'],
            'isolated_phase_root_count':1,'curve_genus':curve.genus,
            'curve_state_dimension':curve.dimension,'curve_connection':matrix_encode(curve.connection)}


def exact_trace_potential_certificate():
    """Restricted continuous-SU(3), fixed-spectrum quartic obstruction."""
    import sympy as s
    r=s.symbols('r1:4');t=s.symbols('t1:4')
    M=s.Matrix([[(r[i]**p-r[2]**p)*(t[j]**q-t[2]**q) for i in range(2) for j in range(2)]
                for p,q in [(1,1),(1,2),(2,1),(2,2)]])
    delta=lambda v:(v[1]-v[0])*(v[2]-v[0])*(v[2]-v[1])
    assert s.factor(M.det()-delta(r)**2*delta(t)**2)==0
    m=s.symbols('m11 m12 m21 m22');k=s.symbols('k');coeff=s.symbols('b1:5')
    H=s.hessian(sum(b*x for b,x in zip(coeff,m))+k*m[0]**2,m)
    assert H.rank()==1
    return {'mixed_trace_coordinate_determinant':'Delta(R)^2 Delta(T)^2',
            'quartic_moment_hessian_rank_at_most':1,
            'conclusion':'No isolated interior CP-violating minimum from fixed-spectrum continuous-SU(3) trace quartics alone.',
            'scope':'Nondegenerate fixed traceless Hermitian spectra and interior unistochastic coordinates. Finite-group quartics lie outside this restriction.'}
