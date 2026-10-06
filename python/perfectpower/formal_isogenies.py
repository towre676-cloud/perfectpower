"""Lift a normalized elliptic tangent map to formal jets, then reconstruct it.

Standard-library exact arithmetic. The source/target 2-isogeny family is
specified; the rational map is reconstructed from its formal logarithm.
"""
from fractions import Fraction as Q
from .exact_linear import kernel
from .rational_functions import RationalFunction as RF
from .symmetry_quotients import XFunction


def mul(a,b,n):return [sum((a[i]*b[k-i] for i in range(max(0,k-len(b)+1),min(k,len(a)-1)+1)),Q(0)) for k in range(n)]
def inv(a,n):
    if not a[0]:raise ValueError('unit series required')
    out=[1/a[0]]
    for k in range(1,n):out.append(-sum((a[i]*out[k-i] for i in range(1,min(k,len(a)-1)+1)),Q(0))/a[0])
    return out
def compose(a,b,n):
    out=[Q(0)]*n
    for c in reversed(a):out=mul(out,b,n);out[0]+=c
    return out
def power(a,k,n):
    out=[Q(1)]+[Q(0)]*(n-1)
    for _ in range(k):out=mul(out,a,n)
    return out


def elliptic_two_isogeny(a,b,order=18):
    a,b=Q(a),Q(b)
    if type(order) is not int or not 12<=order<=40:raise ValueError('formal order 12 through 40 required')
    if not b or not a*a-4*b:raise ValueError('smooth 2-torsion model required')
    n=order+5
    def model(A,B):
        # X=z^2 x satisfies X^2+(A z^2-1)X+B z^4=0.
        X=[Q(1)]
        for k in range(1,n):X.append(-sum((X[i]*X[k-i] for i in range(1,k)),Q(0))-(A*X[k-2] if k>=2 else 0)-(B if k==4 else 0))
        logarithmic=mul([Q(0)]+[k*X[k] for k in range(1,n)],inv(X,n),n)
        differential=[(1 if k==0 else 0)-logarithmic[k]/2 for k in range(n)]
        log=[Q(0)]+[differential[k]/(k+1) for k in range(n-1)]
        return X,log
    X,L=model(a,b);Xt,Lt=model(-2*a,a*a-4*b)
    w=[Q(0),Q(1)]+[Q(0)]*(n-2)
    for k in range(2,n):w[k]=L[k]-compose(Lt,w,k+1)[k]
    if compose(Lt,w,n)!=L:raise AssertionError('formal logarithm lift failed')
    W=w[1:]+[Q(0)];IW=inv(W,n)
    U=mul(compose(Xt,w,n),power(IW,2,n),n)  # z^2 u(z)
    V=mul(mul(compose(Xt,w,n),inv(X,n),n),power(IW,3,n),n) # v(z)/y(z)
    def reconstruct(series,nd,dd,shift):
        # Clear all Laurent powers by z^(2*max(nd,dd)+shift).
        clearance=2*max(nd,dd)+shift;cols=[]
        for deg in range(nd+1):
            s=power(X,deg,n);offset=clearance-2*deg
            cols.append([Q(0)]*offset+s[:n-offset])
        for deg in range(dd+1):
            s=mul(series,power(X,deg,n),n);offset=clearance-2*deg-shift
            cols.append([-v for v in ([Q(0)]*offset+s[:n-offset])])
        basis=kernel(list(zip(*(c[:order] for c in cols))))
        if len(basis)!=1:raise ValueError('formal jets do not uniquely reconstruct the requested bidegree')
        v=basis[0];d=v[nd+1:]
        if not any(d):raise ValueError('zero reconstructed denominator')
        return XFunction([RF([c]) for c in v[:nd+1]],[RF([c]) for c in d])
    u=reconstruct(U,2,1,2);v=reconstruct(V,2,2,0);z=RF([0]);x=XFunction([z,RF([1])])
    p=x*x*x+a*x*x+b*x;q=u*u*u-2*a*u*u+(a*a-4*b)*u
    if p*v*v!=q or u.dx()!=v:raise AssertionError('reconstructed isogeny identities failed')
    return dict(schema='pp-formal-elliptic-isogeny/1',source_a=str(a),source_b=str(b),target_a=str(-2*a),target_b=str(a*a-4*b),order=order,
        tangent_multiplier=1,formal_parameter_map=list(map(str,w[:order])),x_map=u.packet(),y_multiplier=v.packet(),
        algebraic_identity_checked=True,differential_identity_checked=True,map_degree=u.degree(),kernel_point=['0','0'],
        scope='normalized 2-isogeny class; formal differential lifting, unique bounded rational reconstruction and exact verification, not a general correspondence search')
