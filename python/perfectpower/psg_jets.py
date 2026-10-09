"""Finite formal jets with exact parameter coefficients and explicit depth.

Unknown coefficients are never filled with zero to claim higher resolution.
Composition is truncated only after exact coefficient arithmetic.
"""
from fractions import Fraction as Q
from .psg_polynomial import rational
from .psg_algebra import dependency_profile
from . import exact_linear as E
from itertools import product


def _order(order):
    if type(order) is not int or not 0<=order<=64: raise ValueError('jet order in 0..64 required')


def convolution(a,b,order):
    _order(order)
    if not a or not b: raise ValueError('nonempty jets required')
    zero=a[0]*0
    return [sum((a[j]*b[k-j] for j in range(k+1) if j<len(a) and k-j<len(b)),zero)
            for k in range(order+1)]


def compose(outer,inner,order):
    """Known order-n germs with zero inner constant give known order-n pullback."""
    _order(order)
    if len(outer)<order+1 or len(inner)<order+1: raise ValueError('insufficient known jet depth')
    if inner[0]: raise ValueError('formal inner germ must have zero constant')
    zero=inner[0]*0; unit=zero+1
    out=[zero for _ in range(order+1)]; power=[unit]+[zero]*order
    for k in range(order+1):
        out=[x+outer[k]*p for x,p in zip(out,power)]
        power=convolution(power,inner,order)
    return out


def curvature_jet(coefficients,order):
    """I=F''/F': order n needs F through order n+2, and F'(0)≠0."""
    _order(order)
    if len(coefficients)<order+3: raise ValueError('F curvature needs two additional known orders')
    f=list(map(rational,coefficients)); d=[(k+1)*f[k+1] for k in range(order+2)]
    if not d[0]: raise ValueError('nonzero F prime at origin required')
    result=[]
    for k in range(order+1):
        value=((k+1)*d[k+1]-sum((result[j]*d[k-j] for j in range(k)),Q(0)))/d[0]
        result.append(rational(value))
    return {'order':order,'required_source_order':order+2,'coefficients':list(map(str,result)),
            'scope':'exact finite jet of F double prime divided by F prime'}


def schroder_residual(map_jet,lift_jet,multiplier,order):
    """Coefficient equations for Ψ(F(h))=λ Ψ(h); no infinite conjugacy claim."""
    _order(order)
    lam=rational(multiplier)
    if len(map_jet)<order+1 or len(lift_jet)<order+1: raise ValueError('insufficient source depth')
    if map_jet[0] or map_jet[1]!=map_jet[1]*0+lam: raise ValueError('fixed-origin map with declared linear multiplier required')
    composed=compose(lift_jet,map_jet,order)
    return [a-lam*b for a,b in zip(composed,lift_jet)]


def pushforward_profile(outer,inner,order):
    result=compose(outer,inner,order)
    return {'order':order,'coefficients':[p.packet() for p in result],
            'dependencies':dependency_profile(result),
            'scope':'exact known finite-jet composition; no unique infinite extension asserted'}


def differential_model_space(coefficients,jet_order,model_degree,derivative_order=1):
    """Complete coefficient space for a declared finite differential ansatz.

Monomials use h,F,F',...,F^(r). A full-column-rank matrix excludes every
nonzero model in this bounded ansatz at this known jet depth. A kernel vector
is only a finite-order compatible model, not an infinite analytic identity.
"""
    _order(jet_order)
    if type(model_degree) is not int or not 0<=model_degree<=4 or type(derivative_order) is not int or not 0<=derivative_order<=3:
        raise ValueError('model degree 0..4 and derivative order 0..3 required')
    if len(coefficients)<jet_order+derivative_order+1: raise ValueError('insufficient known differential jet depth')
    f=list(map(rational,coefficients));germs=[[Q(0),Q(1)]+[Q(0)]*max(0,jet_order-1)]
    current=f
    for r in range(derivative_order+1):
        germs.append(current[:jet_order+1])
        current=[(k+1)*current[k+1] for k in range(len(current)-1)]
    exponents=[e for e in product(range(model_degree+1),repeat=len(germs)) if sum(e)<=model_degree]
    if len(exponents)>512: raise ValueError('differential ansatz exceeds 512 monomials')
    columns=[]
    for e in exponents:
        value=[Q(1)]+[Q(0)]*jet_order
        for germ,n in zip(germs,e):
            for _ in range(n):value=convolution(value,germ,jet_order)
        columns.append(value)
    matrix=E.transpose(columns);basis=E.kernel(matrix);rank=E.rank(matrix)
    return {'jet_order':jet_order,'required_source_order':jet_order+derivative_order,
            'model_degree':model_degree,'derivative_order':derivative_order,
            'variables':['h','F']+[f'F_derivative_{r}' for r in range(1,derivative_order+1)],
            'monomials':[list(e) for e in exponents],
            'matrix':[[str(q) for q in row] for row in matrix],
            'rank':rank,'nullity':len(basis),'basis':[[str(q) for q in v] for v in basis],
            'status':'bounded_model_excluded' if not basis else 'finite_order_compatible',
            'scope':'complete rational coefficient space for the declared finite differential ansatz and supplied exact jet'}
