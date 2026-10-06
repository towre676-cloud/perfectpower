"""Remove field-tower coefficient poles before rational specialization.

Gauss's lemma clears coefficient denominators and primitive contents. Only
polynomial gcds in at most two variables are needed for a three-level tower.
"""
from fractions import Fraction as Q
from math import prod
from . import polyalg as P
from .core import mul as pmul
from .rational_functions import AlgebraBudget
from .divisor_square import WorkLimit


def check(p,budget):
    budget.work+=1+len(p)
    if budget.work>budget.work_limit:raise WorkLimit('specialization polynomial work budget')
    if any(max(k,default=0)>budget.degree_limit for k in p):raise WorkLimit('specialization polynomial degree budget')
    if any(max(abs(c.numerator).bit_length(),c.denominator.bit_length())>budget.bit_limit for c in p.values()):raise WorkLimit('specialization coefficient bit budget')
    return {k:v for k,v in p.items() if v}


def add(a,b,budget):
    out=dict(a)
    for k,v in b.items():out[k]=out.get(k,Q(0))+v
    return check(out,budget)


def product(a,b,budget):
    out={}
    for k,x in a.items():
        for l,y in b.items():
            key=tuple(i+j for i,j in zip(k,l));out[key]=out.get(key,Q(0))+x*y
    return check(out,budget)


def exact_div(a,b,budget):
    if not b:raise ZeroDivisionError('zero specialization polynomial')
    remainder=dict(a);out={};lead=max(b)
    while remainder:
        k=max(remainder)
        if any(i<j for i,j in zip(k,lead)):raise ArithmeticError('inexact multivariate polynomial division')
        power=tuple(i-j for i,j in zip(k,lead));v=remainder[k]/b[lead];out[power]=out.get(power,Q(0))+v
        for l,c in b.items():
            index=tuple(i+j for i,j in zip(power,l));value=remainder.get(index,Q(0))-v*c
            if value:remainder[index]=value
            else:remainder.pop(index,None)
        check(remainder,budget)
    return check(out,budget)


def coefficients(p,variables):
    degree=max((k[-1] for k in p),default=0);out=[{} for _ in range(degree+1)]
    for k,c in p.items():out[k[-1]][k[:-1]]=c
    return out


def assemble(rows):
    return {k+(i,):c for i,row in enumerate(rows) for k,c in row.items() if c}


def univariate(p):return P.poly(p.get((i,),Q(0)) for i in range(max((k[0] for k in p),default=0)+1))
def sparse(p):return {(i,):c for i,c in enumerate(p) if c}


def polynomial_gcd(a,b,variables,budget):
    if not a:return b
    if not b:return a
    if variables==1:return check(sparse(P.gcd_poly(univariate(a),univariate(b))),budget)
    if variables!=2:raise ValueError('coefficient polynomial gcd in at most two variables')
    from .parameter_functions import ParameterFunction as PF, gcd
    aa,bb=coefficients(a,2),coefficients(b,2)
    ca,cb={},{}
    for p in aa:
        if p:ca=polynomial_gcd(ca,p,1,budget)
    for p in bb:
        if p:cb=polynomial_gcd(cb,p,1,budget)
    content=polynomial_gcd(ca,cb,1,budget)
    field=lambda p:PF(['coefficient'],univariate(p),budget=budget)
    left=[field(exact_div(p,ca,budget)) if p else field({}) for p in aa]
    right=[field(exact_div(p,cb,budget)) if p else field({}) for p in bb]
    common=gcd(left,right,field({}));denominator=P.ONE
    for c in common:denominator=pmul(denominator,P.exact_div(c.d,P.gcd_poly(denominator,c.d)))
    cleared=[pmul(c.n,P.exact_div(denominator,c.d)) for c in common];primitive=P.ZERO
    for p in cleared:primitive=P.gcd_poly(primitive,p)
    rows=[product(content,sparse(P.exact_div(p,primitive)),budget) for p in cleared]
    return check(assemble(rows),budget)


def fraction_polynomials(value,budget=None):
    budget=budget or AlgebraBudget(work_limit=value.budget.work_limit,degree_limit=value.budget.degree_limit,bit_limit=value.budget.bit_limit)
    if len(value.parameters)==1:return sparse(value.n),sparse(value.d)
    variables=len(value.parameters)-1;rows=[];common={(0,)*variables:Q(1)}
    for c in value.n+value.d:
        n,d=fraction_polynomials(c,budget);rows.append((n,d))
        factor=polynomial_gcd(common,d,variables,budget)
        common=product(common,exact_div(d,factor,budget),budget)
    cleared=[product(n,exact_div(common,d,budget),budget) for n,d in rows]
    content={}
    for row in cleared:
        if row:content=polynomial_gcd(content,row,variables,budget)
    cleared=[exact_div(row,content,budget) if row else {} for row in cleared]
    return assemble(cleared[:len(value.n)]),assemble(cleared[len(value.n):])


def evaluate(value,values):
    n,d=fraction_polynomials(value)
    def at(p):return sum((c*prod(v**k for v,k in zip(values,key)) for key,c in p.items()),Q(0))
    denominator=at(d)
    if not denominator:raise ValueError('parameter function pole or indeterminate specialization')
    return at(n)/denominator
