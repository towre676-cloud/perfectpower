"""Pole reduction on y^d=f(x,t), gcd(d,deg f)=1, with exact primitives."""
from copy import deepcopy
from fractions import Fraction as Q
from math import gcd
from .rational_functions import RationalFunction as RF, AlgebraBudget
from . import field_polynomials as F
from .symmetry_quotients import XFunction
from .differential_extensions import encode, matrix_encode
from .differential_modules import DifferentialModule


class RationalPrimitive:
    """Exact unreduced rational x function with a known power-of-f denominator."""
    def __init__(self,n,d):self.n,self.d=F.trim(n),F.trim(d)
    def __bool__(self):return any(self.n)
    def packet(self):return dict(numerator=[encode(v) for v in self.n],denominator=[encode(v) for v in self.d])


class SuperellipticFamily:
    def __init__(self,specification):
        if not isinstance(specification,dict) or set(specification)-{'coefficients','cover_degree','work_limit','degree_limit','bit_limit'}:raise ValueError('coefficients and cover_degree required')
        self.specification=deepcopy(specification)
        self.budget=AlgebraBudget(**{k:specification[k] for k in ('work_limit','degree_limit','bit_limit') if k in specification})
        self.f=F.trim([RF.parse(v,self.budget) for v in specification['coefficients']]);d=specification['cover_degree'];m=len(self.f)-1
        if type(d) is not int or not 2<=d<=8 or not 2<=m<=8 or gcd(d,m)!=1 or (d-1)*(m-1)>32:raise ValueError('coprime cover/polynomial degrees 2 through 8, dimension at most 32 required')
        if self.f[-1]!=1:raise ValueError('monic model required')
        g,u,v=F.extended_gcd(self.f,F.derivative(self.f))
        if len(g)!=1:raise ValueError('generically squarefree model required')
        self.inverse_dx=F.scale(v,1/g[0]);self.d=d;self.m=m;self.zero=self.f[0].coerce(0)
        self.dimension=(d-1)*(m-1);self.genus=self.dimension//2
        self.basis=[(j,i) for j in range(1,d) for i in range(m-1)];self.connection=[];self.primitives=[]
        dt=[v.derivative() for v in self.f]
        for j,i in self.basis:
            h=F.scale([self.zero]*i+dt,-Q(j,d));c,r=self.reduce(h,j,1)
            row=[self.zero]*self.dimension;start=(j-1)*(m-1);row[start:start+m-1]=c
            self.connection.append(row);self.primitives.append(r.packet())

    def reduce(self,numerator,character,pole_order=0):
        if type(character) is not int or not 1<=character<self.d or type(pole_order) is not int or not 0<=pole_order<=24:raise ValueError('supported character and pole order required')
        h=F.trim(numerator);original=h[:];z=self.zero;f=self.f;denpower=max(0,pole_order-1);rn=[z]
        for k in range(pole_order,0,-1):
            b=F.divide(F.product(h,self.inverse_dx),f)[1]
            a,remainder=F.divide(F.add(h,F.scale(F.product(b,F.derivative(f)),-1)),f)
            if any(remainder):raise AssertionError('vertical division failed')
            factor=Q(self.d,character+self.d*(k-1))
            rn=F.add(rn,F.product(F.scale(b,-factor),F.power(f,denpower-k+1)))
            h=F.add(a,F.scale(F.derivative(b),factor))
        while len(h)>self.m-1:
            k=len(h)-self.m;factor=h[-1]/(k+Q((self.d-character)*self.m,self.d))
            primitive=F.product([z]*k+[factor],f)
            exact=F.add(F.derivative(primitive),F.scale(F.product([z]*k+[factor],F.derivative(f)),-Q(character,self.d)))
            h=F.add(h,F.scale(exact,-1));rn=F.add(rn,F.product(primitive,F.power(f,denpower)))
        c=h+[z]*(self.m-1-len(h))
        replay=F.add(F.product(c,F.power(f,denpower+1)),F.add(F.product(F.derivative(rn),f),F.scale(F.product(rn,F.derivative(f)),-(denpower+Q(character,self.d)))))
        if replay!=F.product(original,F.power(f,denpower+1-pole_order)):raise AssertionError('superelliptic primitive replay failed')
        return c,RationalPrimitive(rn,F.power(f,denpower))

    def summary(self):return dict(schema='pp-superelliptic-family/1',cover_degree=self.d,polynomial_degree=self.m,genus=self.genus,dimension=self.dimension)
    def evidence(self):return dict(self.summary(),polynomial=[encode(v) for v in self.f],basis=[dict(character=j,x_power=i,holomorphic=self.m*j>self.d*(i+1)) for j,i in self.basis],
        connection=matrix_encode(self.connection),exact_primitives=self.primitives,reduction_identities_checked=self.dimension,scope='smooth coprime monic superelliptic curves with one point at infinity')
    def observable(self,coefficients=None):return DifferentialModule.from_matrix(self.connection).observable(coefficients)
