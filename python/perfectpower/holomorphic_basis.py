"""Exact differentials on compact normalized complex cyclic components.

Classical valuation construction; no numerical periods and no analytic Lean proof.
The reduced monic equation z^n=R(x) describes one complex component up to scaling.
"""
from fractions import Fraction as Q
from math import gcd
from . import polyalg as P
from .core import mul, power, subtract
from .branched_geometry import profile


def differential_basis(coefficients, d):
    geometry = profile(coefficients, d)
    c, n = geometry['components'], geometry['component_cover_degree']
    blocks = [(b['multiplicity']//c, P.poly([Q(v) for v in b['monic_factor']]))
              for b in geometry['multiplicity_blocks']]
    reduced = P.poly([1])
    for e, f in blocks:
        reduced = mul(reduced, power(f, e))
    degree = P.degree(reduced)
    delta = gcd(n, degree)
    forms, characters = [], []
    for j in range(1, n):
        numerator = P.poly([1])
        for e, f in blocks:
            numerator = mul(numerator, power(f, j*e//n))
        a = P.degree(numerator)
        count = max(0, (j*degree-n*a-delta)//n)
        finite = [{'reduced_multiplicity': e, 'distinct_roots': P.degree(f),
                   'places_per_root': gcd(n,e),
                   'order': (n*(j*e//n)+n-j*e)//gcd(n,e)-1}
                  for e, f in blocks]
        if any(b['order'] < 0 for b in finite):
            raise AssertionError('finite pole in proposed holomorphic form')
        for i in range(count):
            full = mul(P.poly([0]*i+[1]), numerator)
            infinity = (j*degree-n*(a+i)-n)//delta-1
            if infinity < 0:
                raise AssertionError('infinite pole in proposed holomorphic form')
            # Divisor degree of a nonzero differential is 2g-2. x^i adds
            # zeros at zero: if zero is a branch point it adds n*i/h there;
            # otherwise it adds i at each of n unramified points.
            divisor_degree = sum(b['distinct_roots']*b['places_per_root']*b['order'] for b in finite) + n*i + delta*infinity
            if divisor_degree != 2*geometry['genus_per_component']-2:
                raise AssertionError('differential divisor degree mismatch')
            # Coefficient h=N/z^j satisfies A*h'+B*h=0 off zeros/poles.
            op_a = P.scale(mul(reduced,full),n)
            op_b = subtract(P.scale(mul(P.derivative(reduced),full),j),
                         P.scale(mul(reduced,P.derivative(full)),n))
            forms.append({'index': len(forms), 'character_j': j, 'x_power': i,
                          'numerator': list(map(str,full)), 'denominator_z_power': j,
                          'finite_orders_before_x_power': finite,
                          'extra_zero_divisor_degree': n*i,
                          'order_at_each_infinity': infinity,
                          'divisor_degree': divisor_degree,
                          'coefficient_operator': {'derivative':list(map(str,op_a)),
                                                   'zeroth':list(map(str,op_b))}})
        characters.append({'j':j,'deck_eigenvalue_exponent':(-j)%n,
                           'holomorphic_dimension':count})
    dims = {b['j']:b['holomorphic_dimension'] for b in characters}
    for b in characters:
        b['complex_h1_dimension']=dims[b['j']]+dims[n-b['j']]
    g = geometry['genus_per_component']
    if len(forms)!=g or sum(b['complex_h1_dimension'] for b in characters)!=2*g:
        raise AssertionError('basis and character counts disagree with genus')
    return {'schema':'pp-holomorphic-basis/1','geometry':geometry,
            'component_equation':{'power':n,'monic_polynomial':list(map(str,reduced)),
                                  'scalar_normalization':'over C; not an arithmetic descent to Q'},
            'forms_per_component':forms,'characters':characters,
            'dimension_per_component':g,'dimension_all_components':c*g,
            'period_matrix_shape_per_component':[g,2*g],
            'formalized':False,'execution_verified':False,
            'scope':'classical complex normalization basis and exact polynomial operators; no analytic period values'}


def squarefree_character_dimensions(d,m):
    if type(d) is not int or not 2<=d<=64 or type(m) is not int or m<1:
        raise ValueError('power 2..64 and positive degree required')
    delta=gcd(d,m)
    return [max(0,(j*m-delta)//d) for j in range(1,d)]


def normalize_in_basis(packet, period_matrix, candidate_periods, target_periods=None):
    """Correct supplied periods in the explicit basis on ONE component.

Rows are chosen cycles, columns are packet forms. Rational input is a finite
contract; callers must independently establish that it represents real periods.
"""
    from .period_boundary import normalize_periods
    g=packet['dimension_per_component']
    if len(period_matrix)!=g or len(candidate_periods)!=g:
        raise ValueError('one component requires exactly genus many normalization conditions')
    result=normalize_periods(period_matrix,candidate_periods,target_periods)
    result['holomorphic_correction']=[{'coefficient':a,'form':f}
        for a,f in zip(result['correction'],packet['forms_per_component']) if Q(a)!=0]
    result['scope']='explicit holomorphic basis with supplied exact period data; no analytic integration'
    return result
