"""Discover translated-even sextics and execute both elliptic quotient sectors.

The genus-two basis removes residues at infinity explicitly. Its connection
is derived independently, then compared with the pullback elliptic blocks.
"""
from copy import deepcopy
from fractions import Fraction as Q
from . import polyalg as P
from .core import integer_power_root
from .observable_machine import _q
from .rational_functions import RationalFunction as RF, AlgebraBudget, solve_many
from .curve_families import CurveFamily, encode_matrix
from . import field_polynomials as F


def _parse(specification):
    if not isinstance(specification,dict) or set(specification)-{'coefficients','work_limit','degree_limit','bit_limit'} or 'coefficients' not in specification:
        raise ValueError('sextic coefficients and optional algebra budgets required')
    limits={k:specification[k] for k in ('work_limit','degree_limit','bit_limit') if k in specification}
    budget=AlgebraBudget(**limits);coefficients=specification['coefficients']
    if not isinstance(coefficients,(list,tuple)) or len(coefficients)!=7:raise ValueError('monic sextic required')
    f=[RF.parse(a,budget) for a in coefficients]
    if f[-1]!=1 or any(a.d!=P.ONE or P.degree(a.n)>8 for a in f):raise ValueError('monic polynomial sextic with parameter degree at most eight required')
    center=-f[5]/6;centered=F.shift(f,center)
    return f,center,centered,limits,budget


def discover_elliptic_quotients(specification):
    f,center,centered,limits,budget=_parse(specification)
    odd=[centered[i] for i in (1,3,5)];found=not any(odd)
    nonzero=[a.n for a in odd if a]
    common=P.ZERO if not nonzero else nonzero[0]
    for p in nonzero[1:]:common=P.gcd_poly(common,p)
    return dict(schema='pp-even-sextic-discovery/1',found=found,center=center.packet(),
        centered_coefficients=[a.packet() for a in centered],odd_coefficient_conditions=[a.packet() for a in odd],
        symmetry_specialization_polynomial=list(map(str,P.monic(common))),
        reflection='x -> 2 center(t)-x; y -> y',algebra_work=budget.work,
        execution_verified=False,scope='complete translated reflection test for monic sextics over Q(t); zero specialization polynomial means the identities hold generically, and isolated specializations still require smoothness')


def translated_even_specification(A,B,C,center=0):
    """Construct a genus-two candidate from the desired first cubic quotient.

    This returns a specification; EllipticQuotientFamily checks generic
    smoothness and builds both quotient systems when it is registered.
    """
    budget=AlgebraBudget();A,B,C,h=[RF.parse(v,budget) for v in (A,B,C,center)]
    if any(a.d!=P.ONE for a in (A,B,C,h)):raise ValueError('polynomial parameter inputs required')
    z=[-h,h.coerce(1)]
    f=F.add(F.add(F.power(z,6),F.scale(F.power(z,4),A)),F.add(F.scale(F.power(z,2),B),[C]))
    specification=dict(coefficients=[list(map(str,a.n)) for a in f])
    _parse(specification)
    return specification


class EllipticQuotientFamily:
    def __init__(self,specification):
        self.specification=deepcopy(specification)
        self.f,self.center,self.centered,self.limits,budget=_parse(specification)
        if any(self.centered[i] for i in (1,3,5)):raise ValueError('sextic has no translated even reflection; use discover_quotients for the exact conditions')
        self.C,self.B,self.A=self.centered[0],self.centered[2],self.centered[4]
        if not self.C:raise ValueError('zero centered constant gives a singular sextic')
        first=[self.C,self.B,self.A,self.A.coerce(1)]
        second=[self.C*self.C,self.A*self.C,self.B,self.A.coerce(1)]
        # Quotient coordinate changes can raise parameter degree. These
        # derived polynomial inputs retain the exact algebra budgets.
        self.sectors={name:CurveFamily(dict(coefficients=[list(map(str,a.n)) for a in coeff],**self.limits),
            _parameter_degree_limit=128) for name,coeff in [('first',first),('second',second)]}
        self.discriminant=(-64*self.C*RF(self.sectors['first'].discriminant,budget=budget)*RF(self.sectors['first'].discriminant,budget=budget)).n
        expected=RF(self.sectors['first'].discriminant,budget=budget)*self.C*self.C
        if RF(self.sectors['second'].discriminant,budget=budget)!=expected:raise AssertionError('elliptic quotient discriminant identity failed')
        zero=self.A.coerce(0);one=self.A.coerce(1)
        self.basis=[[one],[zero,one],[zero,zero,zero,one],[zero,zero,self.A/2,zero,one]]
        self.connection,self.reductions=self._reduce(budget)
        block=[[zero for _ in range(4)] for _ in range(4)]
        for offset,name in [(0,'first'),(2,'second')]:
            for i,row in enumerate(self.sectors[name].connection):
                for j,a in enumerate(row):block[offset+i][offset+j]=RF.parse(a,budget)
        # chi=(2 eta_1,2 eta_2,-2 eta_0,-4 eta_3), constant invertible map.
        transform=[[zero,2*one,zero,zero],[zero,zero,2*one,zero],[-2*one,zero,zero,zero],[zero,zero,zero,-4*one]]
        if F.matrix_product(transform,self.connection)!=F.matrix_product(block,transform):raise AssertionError('quotient connection does not intertwine')
        self.packet=dict(schema='pp-elliptic-quotient-family/1',genus=2,state_dimension=4,
            discovery=discover_elliptic_quotients(specification),discriminant=list(map(str,self.discriminant)),
            first=self.sectors['first'].evidence(),second=self.sectors['second'].evidence(),
            quotient_maps=dict(first='z=x-center; u=z^2; v=y; v^2=u^3+A u^2+B u+C',
                second_quartic='u=z^2; w=z y; w^2=u(u^3+A u^2+B u+C)',
                second_cubic='X=C/z^2; Y=C y/z^3; Y^2=X^3+B X^2+A C X+C^2; z!=0'),
            basis=['dz/y','z dz/y','z^3 dz/y','(z^4+A z^2/2) dz/y'],
            basis_polynomials=encode_matrix(self.basis),connection=encode_matrix(self.connection),
            exact_derivative_numerators=encode_matrix(self.reductions),
            elliptic_block_connection=encode_matrix(block),pullback_matrix=encode_matrix(transform),
            connection_intertwining_checked=True,exact_reduction_identities_checked=4,
            residue_removal='z^2 dz/y has residues at the two infinities; z^4 dz/y is corrected by A z^2 dz/(2y)',
            second_pullback_exact_term='X dX/Y = -4 eta_3 + 2 d(y/z)',
            discriminant_identities=['disc(P)=-64 C disc(Q)^2','disc(second cubic)=C^2 disc(Q)'],
            algebra_work=budget.work,execution_verified=False,
            scope='exact translated-even-sextic quotient maps and a residue-free four-dimensional de Rham connection; two elliptic sectors, no claim to discover every genus-two elliptic cover')

    def _reduce(self,budget):
        f=[RF.parse(a,budget) for a in self.centered];zero=f[0].coerce(0);size=11
        pad=lambda a:a+[zero]*(size-len(a))
        columns=[pad(F.product(q,f)) for q in self.basis]
        for k in range(6):
            r=[zero]*k+[zero.coerce(1)]
            columns.append(pad(F.add(F.product(F.derivative(r),f),F.scale(F.product(r,F.derivative(f)),-Q(1,2)))))
        dt=[a.derivative() for a in f];targets=[]
        for q in self.basis:
            target=F.add(F.product([a.derivative() for a in q],f),F.scale(F.product(q,dt),-Q(1,2)))
            targets.append(pad(target))
        solution=solve_many(list(map(list,zip(*columns))),list(map(list,zip(*targets))))
        if solution is None:raise AssertionError('residue-free even reduction failed')
        connection=list(map(list,zip(*solution[:4])));reductions=list(map(list,zip(*solution[4:])))
        for i,(row,r) in enumerate(zip(connection,reductions)):
            b=[zero]
            for a,q in zip(row,self.basis):b=F.add(b,F.scale(q,a))
            actual=F.add(F.product(b,f),F.add(F.product(F.derivative(r),f),F.scale(F.product(r,F.derivative(f)),-Q(1,2))))
            if pad(actual)!=targets[i]:raise AssertionError('even de Rham identity mismatch')
        return connection,reductions

    def summary(self):return dict(genus=2,state_dimension=4,elliptic_sectors=2,discriminant=list(map(str,self.discriminant)),complete_for_supported_family=True)
    def evidence(self):return deepcopy(self.packet)
    def _sector(self,sector):
        if sector not in self.sectors:raise ValueError('sector must be first or second')
        return self.sectors[sector]
    def observable(self,sector='first',coefficients=None):
        return dict(sector=sector,operator=self._sector(sector).observable(coefficients),quotient_map=self.packet['quotient_maps'][sector if sector=='first' else 'second_cubic'])
    def collisions(self,sector='first'):return dict(sector=sector,analysis=self._sector(sector).collisions())
    def period_path(self,path,contour,sector='first',coefficients=None,mode='matrix',tolerance=1e-10):
        return dict(sector=sector,continuation=self._sector(sector).period_path(path,contour,coefficients,mode,tolerance),
            scope='marked period execution on the specified elliptic quotient; no identification with an arbitrary genus-two marked cycle')
    def root_motion(self):
        from .curve_structure import root_motion
        return root_motion(self)
    def specialize(self,parameter):
        t=_q(parameter)
        if not P.evaluate(self.discriminant,t):raise ValueError('singular sextic parameter')
        return dict(parameter=t,center=self.center.evaluate(t),A=self.A.evaluate(t),B=self.B.evaluate(t),C=self.C.evaluate(t),
            coefficients=[a.evaluate(t) for a in self.f],connection=[[a.evaluate(t) for a in row] for row in self.connection],
            first=self.sectors['first'].specialize(t),second=self.sectors['second'].specialize(t))
    def point_image(self,parameter,x,y):
        data=self.specialize(parameter);x,y=_q(x),_q(y)
        if y*y!=P.evaluate(data['coefficients'],x):raise ValueError('point does not lie on the sextic')
        z=x-data['center'];u=z*z
        return dict(original=[x,y],first=[u,y],second_quartic=[u,z*y],
            second_cubic=[data['C']/u,data['C']*y/(z*u)] if z else None,
            second_cubic_at_infinity=not z,original_integral=x.denominator==y.denominator==1)
    def rational_lifts(self,parameter,u,v,sector='first'):
        data=self.specialize(parameter);u,v=_q(u),_q(v)
        value=u**3+data['A']*u*u+data['B']*u+data['C']
        if sector not in ('first','second'):raise ValueError('sector must be first or second')
        if v*v!=(value if sector=='first' else u*value):raise ValueError('point does not lie on the declared elliptic quotient')
        n=integer_power_root(u.numerator,2) if u>=0 else None;d=integer_power_root(u.denominator,2)
        points=[]
        if n is not None and d is not None:
            z=Q(n,d);zs=[z] if not z else [-z,z]
            for z in zs:
                if sector=='first':ys=[v]
                elif z:ys=[v/z]
                else:
                    rn=integer_power_root(data['C'].numerator,2) if data['C']>=0 else None
                    rd=integer_power_root(data['C'].denominator,2)
                    ys=[] if rn is None or rd is None else [-Q(rn,rd),Q(rn,rd)]
                for y in ys:
                    x=data['center']+z
                    if y*y!=P.evaluate(data['coefficients'],x):raise AssertionError('quotient lift identity failed')
                    points.append(dict(x=x,y=y,integral=x.denominator==y.denominator==1))
        return dict(sector=sector,point=[u,v],points=points,complete_rational_fibre=True,
            scope='every rational point over this one quotient point; no global rational or integer-point census')
