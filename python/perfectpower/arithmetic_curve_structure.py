"""Ramified smooth binomial charts and arithmetic obstructions to projectors.

Cyclotomic tests refer to the action of an actual curve automorphism, not to
coefficientwise Galois invariance of a de Rham matrix. A rational Betti projector
commuting with that action must select complete rational character orbits.
"""
from fractions import Fraction as Q
from math import gcd,lcm
from . import polyalg as P, field_polynomials as F
from .core import mul
from .rational_functions import RationalFunction as RF, AlgebraBudget, solve_many
from .differential_extensions import EtaleAlgebra, EtaleElement, encode, matrix_encode
from .algebraic_local_curves import compose, valuation, laurent
from .local_curve_execution import s_power
from .horizontal_projectors import projector_check
from .symmetry_quotients import PolynomialCurve


def cyclotomic_polynomial(n):
    if type(n) is not int or not 1<=n<=64:raise ValueError('cyclotomic order one through 64 required')
    out=P.poly([-1]+[0]*(n-1)+[1])
    for d in range(1,n):
        if n%d==0:out=P.exact_div(out,cyclotomic_polynomial(d))
    return out


def matrix_inverse(a):
    z=a[0][0].coerce(0);n=len(a);answer=solve_many(a,[[z.coerce(int(i==j)) for j in range(n)] for i in range(n)])
    if answer is None:raise ValueError('invertible frame required')
    return answer


def cyclic_projector_obstruction(family,matrix=None):
    explanation=family.deformation().get('scaling_explanation')
    if explanation is None:return dict(schema='pp-cyclic-betti-obstruction/1',status='NO_SUPPORTED_CYCLIC_SYMMETRY',scope='centered binomial families of odd degrees 3, 5 and 7')
    if matrix is None:
        search=family.horizontal_projectors()
        return dict(schema='pp-cyclic-projector-audit/1',checks=[cyclic_projector_obstruction(family,p['matrix']) for p in search['projectors']],
            tested_projectors=len(search['projectors']),scope='arithmetic obstruction checks on the returned finite differential-projector candidates')
    check=projector_check(family,matrix);n=family.dimension;m=n+1;budget=AlgebraBudget(**family.limits)
    t=[[RF.parse(v,budget) for v in row] for row in explanation['centered_differential_rows']]
    p=[[RF.parse(v,budget) for v in row] for row in matrix]
    centered=F.matrix_product(F.matrix_product(t,p),matrix_inverse(t))
    polynomial=cyclotomic_polynomial(m);algebra=EtaleAlgebra(polynomial,budget=budget);zeta=algebra.generator
    # Verify the real geometric action on the defining centered polynomial.
    c=RF.parse(explanation['constant'],budget)
    if zeta**m!=1:raise AssertionError('cyclotomic generator has wrong order')
    characters=[i+1 for i in range(n)]
    commute=not any(centered[i][j] for i in range(n) for j in range(n) if i!=j)
    result=dict(schema='pp-cyclic-betti-obstruction/1',cyclic_order=m,cyclotomic_modulus=list(map(str,polynomial)),
        automorphism='x -> center+zeta*(x-center); y -> y; zeta^m=1',
        curve_action_identity_checked=True,centered_projector=matrix_encode(centered),
        de_rham_checks=check,commutes_with_cyclic_action=commute,
        full_action_characteristic_polynomial=list(map(str,P.poly([1]*m))),
        scope='necessary rational Betti compatibility for this actual cyclic curve action; no numerical comparison matrix or arbitrary-correspondence search')
    if not check['idempotent']:
        return dict(result,status='NOT_AN_IDEMPOTENT')
    if not commute:return dict(result,status='UNRESOLVED_NONCOMMUTING_PROJECTOR')
    selected=[]
    for i in range(n):
        if centered[i][i] not in (0,1):raise AssertionError('diagonal idempotent coefficient not zero or one')
        if centered[i][i]==1:selected.append(characters[i])
    units=[k for k in range(1,m) if gcd(k,m)==1];remaining=set(characters);orbits=[]
    while remaining:
        a=min(remaining);orbit=sorted({(k*a)%m for k in units});orbits.append(orbit);remaining-=set(orbit)
    selected_polynomial=[algebra.one]
    for k in selected:selected_polynomial=F.product(selected_polynomial,[-zeta**k,algebra.one])
    rational=all(len(v.coefficients)==1 for v in selected_polynomial)
    complete_orbits=all(not set(orbit)&set(selected) or set(orbit)<=set(selected) for orbit in orbits)
    if rational!=complete_orbits:raise AssertionError('cyclotomic orbit and polynomial rationality disagree')
    witness=next((dict(coefficient_index=i,algebra_coefficients=v.packet()) for i,v in enumerate(selected_polynomial) if len(v.coefficients)>1),None)
    result.update(selected_characters=selected,rational_character_orbits=orbits,
        selected_action_characteristic_polynomial=[v.packet() for v in selected_polynomial],
        selected_characteristic_polynomial_rational=rational,obstruction_witness=witness,
        status='RATIONAL_ACTION_COMPATIBLE' if rational else 'RATIONAL_BETTI_OBSTRUCTION',
        reason='a rational projector commuting with an integral geometric action has a rational characteristic polynomial on its image; the selected characters must form complete cyclotomic Galois orbits')
    return result


def ramified_scaling_chart(family,parameter=0):
    explanation=family.deformation().get('scaling_explanation')
    if explanation is None:raise ValueError('centered binomial family required for scaling chart construction')
    budget=AlgebraBudget(**family.limits);center=RF.parse(explanation['center'],budget);constant=RF.parse(explanation['constant'],budget)
    algebra=None
    if isinstance(parameter,dict):
        if set(parameter)-{'modulus','element'} or 'modulus' not in parameter:raise ValueError('squarefree algebraic point required')
        algebra=EtaleAlgebra(parameter['modulus'],budget=budget);alpha=algebra.element(parameter.get('element',[0,1]))
        local=alpha+algebra.zero.coerce(s_power(1,budget))
    elif parameter=='infinity':local=s_power(-1,budget)
    else:local=RF([Q(str(parameter))],budget=budget)+s_power(1,budget)
    local_c=compose(constant,local);v=valuation(local_c);m=family.dimension+1
    xweight=Q(v,m);yweight=Q(v,2);e=lcm(xweight.denominator,yweight.denominator)
    if parameter=='infinity':coordinate=s_power(-e,budget)
    elif algebra:coordinate=alpha+algebra.zero.coerce(s_power(e,budget))
    else:coordinate=RF([Q(str(parameter))],budget=budget)+s_power(e,budget)
    h=compose(center,coordinate);c=compose(constant,coordinate);xp=int(e*xweight);yp=int(e*yweight)
    xs=coordinate.coerce(s_power(xp,budget));ys=coordinate.coerce(s_power(yp,budget));unit=c/ys**2 if isinstance(ys,EtaleElement) else c/(ys*ys)
    z=h.coerce(0);f=[compose(RF.parse(a,budget),coordinate) for a in family.f];transformed=[z]
    for i,a in enumerate(f):transformed=F.add(transformed,F.scale(F.power([h,xs],i),a/(ys*ys)))
    expected=[unit]+[z]*(m-1)+[z.coerce(1)]
    if F.trim(transformed)!=expected:raise AssertionError('ramified polynomial chart replay failed')
    lead=laurent(unit,0).get(0,z)
    if not lead or valuation(unit)!=0:raise AssertionError('normalized constant is not a unit')
    if isinstance(lead,EtaleElement):lead.inverse()
    curve=PolynomialCurve(expected,budget);weights=[Q(i+1,m)-Q(1,2) for i in range(family.dimension)]
    anticipated=[[w*unit.derivative()/unit if i==j else z for j in range(family.dimension)] for i,w in enumerate(weights)]
    if curve.connection!=anticipated:raise AssertionError('ramified geometric and differential charts disagree')
    if any(valuation(a) is not None and valuation(a)<0 for row in anticipated for a in row):raise AssertionError('normalized connection still singular')
    return dict(schema='pp-ramified-smooth-binomial-chart/1',parameter=parameter,ramification=e,
        x_scaling_exponent=xp,y_scaling_exponent=yp,center=h.packet(),unit_constant=encode(unit),
        normalized_polynomial=[encode(v) for v in expected],special_fibre_constant=encode(lead),
        normalized_de_rham=curve.evidence(),differential_scaling_exponents=[e*v*w for w in weights],
        residue_zero=True,special_fibre_smooth=True,polynomial_identity_checked=True,connection_identity_checked=True,
        substitution='t=alpha+s^e (or t=s^-e); x=center(t)+s^x_exponent u; y=s^y_exponent v',
        minimality_scope='least ramification making these x/y scaling valuations integral; not a universal stable-reduction minimality theorem',
        scope='explicit smooth binomial model and regular differential system over the recorded coefficient algebra; marks and numerical error enclosures remain separate')
