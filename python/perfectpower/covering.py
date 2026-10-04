"""Binary-quartic arithmetic and a source-backed Fisher Example 3.4 replay.

No generic Selmer solver or Lean theorem is claimed. The explicit global
conclusion depends on Fisher's pairing theorem, descent and good-prime argument.
Every algebraic and finite local calculation below is recomputed exactly.
"""
from fractions import Fraction as Q
from math import isqrt, prod
from .quotient_algebra import QuotientAlgebra
from .local_quartic import _prime

FISHER_SOURCE='https://arxiv.org/abs/2208.14977'
FISHER_QUARTICS=((-11,68,-52,-164,-64),(-4,-60,-232,-52,-3),(-31,-78,32,102,-53))


def quartic(coefficients):
    a=tuple(map(Q,coefficients))
    if len(a)!=5:
        raise ValueError('five descending binary-quartic coefficients required')
    return a


def evaluate(g,x,z):
    return sum(c*Q(x)**(4-i)*Q(z)**i for i,c in enumerate(quartic(g)))


def invariants(g):
    a,b,c,d,e=quartic(g)
    I=12*a*e-3*b*d+c*c
    J=72*a*c*e-27*a*d*d-27*b*b*e+9*b*c*d-2*c**3
    return I,J,16*(4*I**3-J**2)/27


def hessian(g):
    a,b,c,d,e=quartic(g)
    return (3*b*b-8*a*c,4*(b*c-6*a*d),
            2*(2*c*c-24*a*e-3*b*d),4*(c*d-6*b*e),3*d*d-8*c*e)


def fisher_gamma(g1,g2,g3,m_coefficients):
    """Check m²=z(g1)z(g2)z(g3), then compute gamma by Fisher (3)-(5).

    Quotient algebra is used as algebra, not as an unproved number field.
    A matching invariant pair and nonsingular discriminant are required.
    """
    forms=tuple(map(quartic,(g1,g2,g3)))
    I,J,D=invariants(forms[0])
    if D==0 or any(invariants(g)!=(I,J,D) for g in forms):
        raise ValueError('matching nonsingular quartic invariants required')
    algebra=QuotientAlgebra((J,-3*I,0,1));phi=algebra.element((0,1))
    def cubic(g):
        a,b,c,_,_=g
        return algebra.element((Q(3)*b*b-Q(8)*a*c)/3)+phi*algebra.element(4*a/3)
    z1,z2,z3=map(cubic,forms);m=algebra.element(m_coefficients)
    if m*m != z1*z2*z3:
        raise ValueError('supplied cubic square identity is false')
    factor=z2*z3*m.inverse()
    G=[phi*algebra.element(4*c/3)+algebra.element(h/3)
       for c,h in zip(forms[0],hessian(forms[0]))]
    H=(G[0],G[1]*algebra.element(Q(1,2)),
       G[2]*algebra.element(Q(1,6))+(algebra.element(I)-phi*phi)*algebra.element(Q(2,9)))
    # Recheck G(1,0)*G(x,z)=H(x,z)^2 coefficient by coefficient.
    HH=[algebra.element(0) for _ in range(5)]
    for i,x in enumerate(H):
        for j,y in enumerate(H):HH[i+j]=HH[i+j]+x*y
    if any(z1*g!=hh for g,hh in zip(G,HH)):
        raise AssertionError('quartic covariant identity failed')
    result=[factor*x for x in H]
    return tuple(x.coefficients[2] if len(x.coefficients)>2 else Q(0) for x in result)


def valuation_unit(a,p):
    a=Q(a)
    if a==0:raise ValueError('nonzero Hilbert argument required')
    v=0;n,d=a.numerator,a.denominator
    while n%p==0:n//=p;v+=1
    while d%p==0:d//=p;v-=1
    return v,Q(n,d)


def hilbert(a,b,place):
    """Rational Hilbert symbol at a certified prime or the real place."""
    a,b=Q(a),Q(b)
    if not a or not b:raise ValueError('nonzero Hilbert arguments required')
    if place=='infinity':return -1 if a<0 and b<0 else 1
    if not _prime(place):raise ValueError('prime or infinity required')
    p=place;alpha,u=valuation_unit(a,p);beta,v=valuation_unit(b,p)
    modulus=8 if p==2 else p
    uu=u.numerator*pow(u.denominator,-1,modulus)%modulus
    vv=v.numerator*pow(v.denominator,-1,modulus)%modulus
    if p==2:
        exponent=((uu-1)//2)*((vv-1)//2)+alpha*((vv*vv-1)//8)+beta*((uu*uu-1)//8)
        return -1 if exponent%2 else 1
    legendre=lambda x: -1 if pow(x,(p-1)//2,p)==p-1 else 1
    return (-1 if (alpha*beta*((p-1)//2))%2 else 1)*legendre(uu)**(beta%2)*legendre(vv)**(alpha%2)


def polynomial_value(coefficients,x):
    y=0
    for c in reversed(coefficients):y=y*x+c
    return y


def hensel_simple(coefficients,p,seed,exponent):
    """Exact root modulo p^exponent from a simple root modulo p."""
    if not _prime(p) or type(exponent) is not int or exponent<1 or type(seed) is not int:
        raise ValueError('prime, integer seed and positive exponent required')
    f=tuple(coefficients)
    if not f or any(type(c) is not int for c in f):raise ValueError('integer polynomial required')
    derivative=tuple(i*f[i] for i in range(1,len(f)))
    if polynomial_value(f,seed)%p or polynomial_value(derivative,seed)%p==0:
        raise ValueError('not a simple root modulo p')
    x=seed%p;mod=p
    for _ in range(1,exponent):
        digit=-(polynomial_value(f,x)//mod)*pow(polynomial_value(derivative,x),-1,p)%p
        x+=digit*mod;mod*=p
    return {'prime':p,'exponent':exponent,'root':x,'modulus':mod,
            'residual':polynomial_value(f,x)%mod,'execution_verified':False}


def fisher_571_replay():
    g1,g2,g3=FISHER_QUARTICS
    gamma=fisher_gamma(g1,g2,g3,(Q(936032,9),Q(-8656,9),Q(20,9)))
    expected=(Q(20,9),Q(-64,9),Q(-16,3))
    if gamma!=expected:raise AssertionError('Fisher gamma mismatch')
    core=lambda x,z:5*x*x-16*x*z-12*z*z
    witnesses={3:(1,1,0),5:(0,1,1),7:(1,1,1),11:(3,3,1),571:(2,195,1)}
    local=[]
    # gamma differs from core by the rational square (2/3)^2.
    for p,(x,y,z) in witnesses.items():
        value=int(evaluate(g1,x,z))
        if (value-y*y)%p or core(x,z)%p==0:
            raise AssertionError('invalid odd-prime witness')
        # Smoothness of y²-g1 on one of the two projective base charts.
        dx=sum((4-i)*g1[i]*x**(3-i)*z**i for i in range(4))
        dz=sum(i*g1[i]*x**(4-i)*z**(i-1) for i in range(1,5))
        if (2*y)%p==0 and dx%p==0 and dz%p==0:
            raise AssertionError('singular local witness')
        local.append({'place':p,'point':[x,y,z],'quartic_residue':value%p,
                      'gamma_core_residue':core(x,z)%p,
                      'symbol':hilbert(-4,core(x,z),p)})
    q=(-16,-41,-13,17,-3)
    # Polynomial identity g1(x,1)=x^4+4q(x), low-to-high comparison.
    if tuple(reversed(g1))!=tuple(4*c+(1 if i==4 else 0) for i,c in enumerate(q)):
        raise AssertionError('2-adic square identity failed')
    lift=hensel_simple(q,2,16,12)
    if lift['root']%32!=16 or (core(lift['root'],1)//4)%8!=5:
        raise AssertionError('2-adic square class mismatch')
    local.append({'place':2,'hensel':lift,'gamma_square_class':5,'symbol':hilbert(-4,5,2)})
    if evaluate(g1,15,4)<=0 or core(15,4)>=0:raise AssertionError('real witness failed')
    local.append({'place':'infinity','point':[15,4],'quartic_value':int(evaluate(g1,15,4)),
                  'gamma_core':core(15,4),'symbol':hilbert(-4,core(15,4),'infinity')})
    product=prod(row['symbol'] for row in local)
    if product!=-1:raise AssertionError('pairing product failed')
    return {'schema':'pp-covering/1','quartics':[list(g) for g in FISHER_QUARTICS],
            'invariants':list(map(str,invariants(g1))), 'gamma':list(map(str,gamma)),
            'local_checks':local,'finite_product':product,
            'pairing_matrix_mod2':[[0,1],[1,0]],'execution_verified':False,
            'source':FISHER_SOURCE,'source_example':'3.4',
            'status':'SOURCE_BACKED_OBSTRUCTION_REPLAY',
            'global_dependencies':['Fisher Theorem 3.1 and Example 3.4',
                'source 2-descent identifies the quartics as Selmer classes',
                'source good-prime argument covers all unlisted places'],
            'lean_certified':False,'general_selmer_solver':False}


def two_isogeny_cover(A,B,d):
    """Integral quartic w²=d*u⁴+A*u²*v²+(B/d)*v⁴.

    For nonzero d dividing B, this maps to y²=x³+A*x²+B*x by
    x=d*u²/v², y=d*u*w/v³. This is a covering identity, not completeness
    of square-class representatives or a Selmer computation.
    """
    if any(type(x) is not int for x in (A,B,d)) or not d or not B or B%d:
        raise ValueError('nonzero integer d dividing nonzero B required')
    if A*A==4*B:raise ValueError('nonsingular two-torsion model required')
    return (d,0,A,0,B//d)


def covering_point(A,B,d,u,w,v=1):
    g=two_isogeny_cover(A,B,d);u,w,v=map(Q,(u,w,v))
    if not v or w*w!=evaluate(g,u,v):
        raise ValueError('finite rational covering point required')
    x=d*u*u/(v*v);y=d*u*w/(v**3)
    if y*y!=x**3+A*x*x+B*x:raise AssertionError('covering residual failed')
    return (x,y)


def two_isogeny_point(A,B,x,y):
    """Rational degree-two map on the affine chart x≠0; no point search."""
    two_isogeny_cover(A,B,1);x,y=Q(x),Q(y)
    if not x or y*y!=x**3+A*x*x+B*x:
        raise ValueError('curve point with x nonzero required')
    X=x+A+Q(B)/x;Y=y*(1-Q(B)/(x*x))
    target_A,target_B=-2*A,A*A-4*B
    if Y*Y!=X**3+target_A*X*X+target_B*X:
        raise AssertionError('isogeny residual failed')
    return (X,Y)
