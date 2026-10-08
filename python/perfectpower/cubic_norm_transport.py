"""Exact nonmonic binary-cubic norm transport, with its denominator domain.

For F(r,s)=a*r^3+b*r^2*s+c*r*s^2+d*s^3, t=a*theta satisfies
G(t)=t^3+b*t^2+a*c*t+a^2*d. Norm(a*r-s*t)=a^2*F(r,s).
The reverse coefficient transport requires the constant coefficient to be
divisible by a. Solving an unrestricted norm equation would lose that domain.
"""
from fractions import Fraction as Q
from . import polyalg as P
from .elliptic_two_descent import determinant


def monic_model(coefficients):
    if type(coefficients) not in (list,tuple) or len(coefficients)!=4 or any(type(x) is not int or abs(x).bit_length()>4096 for x in coefficients):
        raise ValueError('four bounded literal integer coefficients required')
    d,c,b,a=coefficients
    if not a:raise ValueError('nonzero cubic leading coefficient required')
    return [a*a*d,a*c,b,1]


def algebra_norm(polynomial, element):
    f=P.poly(polynomial); h=P.poly(element)
    if len(f)!=4 or f[-1]!=1 or len(h)>3:raise ValueError('monic cubic and quadratic element required')
    columns=[]
    for j in range(3):
        value=list(P.mul(h,[Q(0)]*j+[Q(1)]))
        while len(value)>3:
            lead=value.pop();offset=len(value)-3
            for i in range(3):value[offset+i]-=lead*f[i]
        columns.append(value+[Q(0)]*(3-len(value)))
    return determinant([list(row) for row in zip(*columns)])


def binary_cubic_norm(coefficients,r,s):
    model=monic_model(coefficients)
    if type(r) is not int or type(s) is not int:raise ValueError('literal integer source coordinates required')
    d,c,b,a=coefficients
    value=a*r**3+b*r*r*s+c*r*s*s+d*s**3
    element=[a*r,-s,0]; norm=algebra_norm(model,element)
    if norm!=a*a*value:raise ArithmeticError('nonmonic norm identity failed')
    return dict(source_coefficients=list(coefficients),source_coordinates=[r,s],
                monic_polynomial=model,element=element,norm=int(norm),source_value=value,
                norm_multiplier=a*a,constant_divisibility=abs(a))


def recover_binary_coordinates(coefficients,element):
    monic_model(coefficients);a=coefficients[-1]
    if type(element) not in (list,tuple) or len(element)!=3 or any(type(x) is not int for x in element):
        raise ValueError('three literal integer coefficients required')
    u,v,w=element
    if w or u%a:raise ValueError('element is outside the transported binary source domain')
    return [u//a,-v]
