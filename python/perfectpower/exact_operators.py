"""Sparse exact Weyl algebra and polynomial CRT projectors.

Recovered from the tube operator and Wilson-current work. Weyl words use
normal form t^i D^j, so D*t=t*D+1 is enforced in multiplication. A finite
series residual is not a theorem about analytic continuation or zeta values.
"""
from fractions import Fraction as Q
from math import comb, prod
from . import polyalg as P
from .core import mul
from .quotient_algebra import QuotientAlgebra


class Weyl:
    def __init__(self,terms=None):
        self.terms={}
        for (i,j),value in (terms or {}).items():
            if type(i) is not int or type(j) is not int or i<0 or j<0 or type(value) not in (int,Q):
                raise ValueError('nonnegative Weyl degrees and exact rational coefficients required')
            if value:self.terms[i,j]=Q(value)

    @staticmethod
    def coerce(other):return other if isinstance(other,Weyl) else Weyl({(0,0):other})

    def __add__(self,other):
        other=self.coerce(other);terms=self.terms.copy()
        for key,value in other.terms.items():terms[key]=terms.get(key,0)+value
        return Weyl(terms)
    __radd__=__add__
    def __neg__(self):return Weyl({k:-v for k,v in self.terms.items()})
    def __sub__(self,other):return self+-self.coerce(other)
    def __rsub__(self,other):return self.coerce(other)+-self

    def __mul__(self,other):
        other=self.coerce(other);terms={}
        for (i,j),a in self.terms.items():
            for (k,l),b in other.terms.items():
                for r in range(min(j,k)+1):
                    key=(i+k-r,j+l-r)
                    value=a*b*comb(j,r)*prod(range(k-r+1,k+1))
                    terms[key]=terms.get(key,0)+value
        return Weyl(terms)
    __rmul__=__mul__

    def __pow__(self,n):
        if type(n) is not int or n<0:raise ValueError('nonnegative operator power required')
        result=Weyl.coerce(1);base=self
        while n:
            if n&1:result=result*base
            base=base*base;n//=2
        return result

    def __eq__(self,other):return self.terms==self.coerce(other).terms

    def act_series(self,series,count):
        series=tuple(series)
        if type(count) is not int or count<0 or any(type(x) not in (int,Q) for x in series):
            raise ValueError('exact series and nonnegative coefficient count required')
        out=[]
        for m in range(count):
            value=Q(0)
            for (i,j),c in self.terms.items():
                if m<i:continue
                n=m-i+j
                if n>=len(series):raise ValueError('insufficient input coefficients for operator action')
                value+=c*series[n]*prod(range(n-j+1,n+1))
            out.append(value)
        return out

    def receipt(self):return [{'t_degree':i,'D_degree':j,'coefficient':str(c)}
                             for (i,j),c in sorted(self.terms.items())]


def hypergeometric_replay(count=24):
    if type(count) is not int or count<1:raise ValueError('positive replay length required')
    t=Weyl({(1,0):1});D=Weyl({(0,1):1});theta=t*D
    operator=theta*(theta-Q(1,4))*(theta-Q(3,4))-t*(theta+1)**3
    series=[Q(1)]
    for n in range(1,count):series.append(series[-1]*Q(16*n*n,(4*n-3)*(4*n-1)))
    residual=operator.act_series(series,count)
    if any(residual):raise AssertionError('hypergeometric coefficient recurrence failed')
    return {'operator':operator.receipt(),'series_prefix':list(map(str,series)),
            'residuals':list(map(str,residual)),'status':'EXACT_FORMAL_PREFIX_REPLAY',
            'execution_verified':False,'analytic_continuation_proved':False,'zeta_identity_proved':False}


def quotient_projectors(modulus,factors):
    """Idempotents for supplied pairwise-coprime factors, including primary powers."""
    modulus=P.monic(P.poly(modulus));factors=tuple(P.monic(P.poly(f)) for f in factors)
    if P.degree(modulus)<1 or not factors or any(P.degree(f)<1 for f in factors):
        raise ValueError('positive-degree modulus and factors required')
    product=P.ONE
    for f in factors:product=mul(product,f)
    if product!=modulus:raise ValueError('factors do not multiply to the modulus')
    algebra=QuotientAlgebra(modulus);projectors=[]
    for f in factors:
        q=P.exact_div(modulus,f)
        inverse=QuotientAlgebra(f).element(q).inverse().coefficients
        projectors.append(algebra.element(mul(q,inverse)))
    zero=algebra.element(0);one=algebra.element(1)
    if sum(projectors,zero)!=one or any(e*e!=e for e in projectors) or any(
            e*f!=zero for i,e in enumerate(projectors) for f in projectors[i+1:]):
        raise AssertionError('projector identities failed')
    return {'modulus':list(map(str,modulus)), 'factors':[list(map(str,f)) for f in factors],
            'projectors':[list(map(str,e.coefficients)) for e in projectors],
            'execution_verified':False,'scope':'exact identities in the supplied rational polynomial quotient'}
