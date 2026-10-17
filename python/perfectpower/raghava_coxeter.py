"""Raghava inverse-binomial moments of actual Coxeter operators.

One operator L=2I+T+T^-1 supplies both Raghava moments and the real even
Mellin traces of T.  The finite Bernoulli transform is triangular and
invertible.  Cyclic induction is transported to an explicit moment matrix,
which that transform diagonalizes.  These are derived consequences of the
classical arcsine identity (Raghava, Eq. 2.2) and Bernoulli Fourier series
(DLMF 24.8.1), not a historical novelty or analytic Lean-kernel claim.

For phase exp(2*pi*i*q), 0<=q<1, the j-th normalized moment is
  r_j = 4^j/(2j)! * sum multiplicity*(q-1/2)^(2j).
Thus Tr R_j(L)=pi^(2j)*r_j, where
  R_j(L)=sum_(n>=1) e_(j-1)(n)*L^n/(n^2*binom(2n,n)).
At eigenvalue L=4 the scalar identity extends by monotone convergence;
this endpoint is needed by the adjoint spectrum but not the reflection.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import comb, factorial

from .cyclotomic_real import cosine_interval, pi_interval
from .e8_periods import (EXPONENTS, bernoulli_polynomial, coxeter_matrix,
                         identity, matmul, matrix_power)
from .period_transport import PhaseObject, even_period_coefficient, root_fiber
from .raghava_periods import ARCSINE_SOURCE

SOURCES = (ARCSINE_SOURCE, 'https://dlmf.nist.gov/24.8.E1')
MAX_ORDER = 32
MAX_TERMS = 4096
REFLECTION_ANNIHILATOR = (1, -8, 14, -7, 1)
REFLECTION_INITIAL_TRACES = (8, 14, 42, 146)


def _index(value, minimum, maximum, name):
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError('%s must be an integer in [%d,%d]' % (name, minimum, maximum))
    return value


def _degree(value):
    if type(value) is not int or value < 1 or value.bit_length() > 4096:
        raise ValueError('positive induction degree with at most 4096 bits required')
    return value


def e8_reflection_spectrum():
    return PhaseObject(30, tuple((q, 1) for q in EXPONENTS))


def e8_adjoint_spectrum():
    """The spectrum of the actual adjoint lift constructed in e8_lift.py."""
    return PhaseObject(30, tuple((q, 8 + int(q in EXPONENTS)) for q in range(30)))


def angle_moment_coefficient(spectrum, order):
    """Exact coefficient of pi^(2j) in the operator Raghava moment; j=0 is dim."""
    _index(order, 0, MAX_ORDER, 'moment order')
    if not isinstance(spectrum, PhaseObject):
        raise ValueError('a PhaseObject is required')
    if order == 0:
        return spectrum.dimension
    return Q(4**order, factorial(2*order))*sum(
        (a*(q-Q(1, 2))**(2*order) for q, a in spectrum.phases()), Q(0))


def moment_vector(spectrum, order):
    _index(order, 0, MAX_ORDER, 'moment order')
    return tuple(angle_moment_coefficient(spectrum, j) for j in range(order+1))


@lru_cache(maxsize=33)
def bernoulli_bridge_matrix(order):
    """Map (dim,r1,...,rK) to (dim,Z(2)/pi²,...,Z(2K)/pi^(2K))."""
    _index(order, 0, MAX_ORDER, 'bridge order')
    rows = [(Q(1),)+(Q(0),)*order]
    for k in range(1, order+1):
        rows.append(tuple(
            Q((-1)**(k+1)*4**(k-j), 2*factorial(2*(k-j)))
            *bernoulli_polynomial(2*(k-j), Q(1, 2)) if j <= k else Q(0)
            for j in range(order+1)))
    return tuple(rows)


def apply_matrix(matrix, vector):
    vector = tuple(Q(x) for x in vector)
    if any(len(row) != len(vector) for row in matrix):
        raise ValueError('incompatible matrix and vector dimensions')
    return tuple(sum((Q(a)*b for a, b in zip(row, vector)), Q(0)) for row in matrix)


def mellin_from_moments(moments):
    moments = tuple(Q(x) for x in moments)
    _index(len(moments)-1, 0, MAX_ORDER, 'moment vector order')
    return apply_matrix(bernoulli_bridge_matrix(len(moments)-1), moments)


def moments_from_mellin(mellin):
    """Exact triangular inverse; no numerical independence assumption."""
    mellin = tuple(Q(x) for x in mellin)
    _index(len(mellin)-1, 0, MAX_ORDER, 'Mellin vector order')
    matrix = bernoulli_bridge_matrix(len(mellin)-1)
    answer = []
    for i, value in enumerate(mellin):
        answer.append((value-sum((matrix[i][j]*answer[j] for j in range(i)), Q(0)))/matrix[i][i])
    return tuple(answer)


@lru_cache(maxsize=4096)
def _centered_power_sum(degree, even_power):
    # Faulhaber's identity, avoiding allocation of `degree` branches.
    order = even_power+1
    return (bernoulli_polynomial(order, Q(degree+1, 2))
            -bernoulli_polynomial(order, Q(1-degree, 2)))/order


def induction_moment_matrix(degree, order):
    """Actual cyclic induction on normalized Raghava moments, all finite orders.

    A[j,k]=4^(j-k)/(2(j-k))! * d^(-2j)
             *sum_(r=0)^(d-1)(r-(d-1)/2)^(2(j-k)).
    Its diagonal is d^(1-2j).  Degree need not be enumerated.
    """
    degree = _degree(degree)
    _index(order, 0, MAX_ORDER, 'induction moment order')
    return tuple(tuple(
        Q(4**(j-k), factorial(2*(j-k))*degree**(2*j))
        *_centered_power_sum(degree, 2*(j-k)) if k <= j else Q(0)
        for k in range(order+1)) for j in range(order+1))


def induce_spectrum(spectrum, degree, *, branch_budget=200000):
    degree = _degree(degree)
    _index(branch_budget, 1, 1000000, 'branch budget')
    if not isinstance(spectrum, PhaseObject) or len(spectrum.terms)*degree > branch_budget:
        raise ValueError('phase object missing or explicit induction exceeds branch budget')
    n = spectrum.conductor
    return PhaseObject(n*degree, tuple((q+n*r, a)
        for q, a in spectrum.terms for r in range(degree)))


def weight_two_defect(spectrum):
    """r1-dim/6 = 2 Z(2)/pi², natural under induction with multiplier 1/d."""
    return angle_moment_coefficient(spectrum, 1)-spectrum.dimension/6


def e8_reflection_operator():
    """Actual integral 8x8 Lplus=2I+C+C^-1 in the existing simple-root basis."""
    c = coxeter_matrix()
    ci = matrix_power(c, 29)
    return tuple(tuple(2*int(i == j)+c[i][j]+ci[i][j] for j in range(8)) for i in range(8))


def _matrix_add_scaled(left, right, coefficient):
    return tuple(tuple(a+coefficient*b for a, b in zip(row, other)) for row, other in zip(left, right))


def _trace(matrix):
    return sum(matrix[i][i] for i in range(len(matrix)))


def reflection_operator_checks():
    """Recompute the operator polynomial and initial traces from actual C."""
    operator = e8_reflection_operator()
    if matrix_power(coxeter_matrix(), 30) != identity():
        raise ArithmeticError('actual Coxeter matrix did not have thirtieth power one')
    power, value = identity(), tuple((0,)*8 for _ in range(8))
    initial = []
    for i, coefficient in enumerate(REFLECTION_ANNIHILATOR):
        if i < 4:
            initial.append(_trace(power))
        value = _matrix_add_scaled(value, power, coefficient)
        power = matmul(operator, power)
    if any(x for row in value for x in row) or tuple(initial) != REFLECTION_INITIAL_TRACES:
        raise ArithmeticError('actual reflection operator failed the recurrence certificate')
    return dict(dimension=8, annihilator=list(REFLECTION_ANNIHILATOR),
                initial_traces=initial, exact_matrix_polynomial_zero=True, coxeter_thirtieth_power_identity=True)


def reflection_trace_sequence(terms):
    """Tr(Lplus^n), n=0,...,terms, via its proven finite annihilator."""
    _index(terms, 0, MAX_TERMS, 'trace terms')
    values = list(REFLECTION_INITIAL_TRACES[:terms+1])
    for n in range(4, terms+1):
        values.append(7*values[-1]-14*values[-2]+8*values[-3]-values[-4])
    return tuple(values)


def _outward(interval, bits):
    scale = 1 << bits
    lower, upper = interval
    return (Q((lower*scale).numerator//(lower*scale).denominator, scale),
            Q(-((-upper*scale).numerator//(-upper*scale).denominator), scale))


def _positive_series_enclosure(order, trace, rank, coefficient, bits, schema):
    terms = len(trace)-1
    elementary = [Q(1)]+[Q(0)]*(order-1)
    partial = Q(0)
    for n in range(1, terms+1):
        partial += elementary[-1]*trace[n]/(n*n*comb(2*n, n))
        for j in range(order-1, 0, -1):
            elementary[j] += elementary[j-1]/(n*n)
    _, cosine_upper = cosine_interval(30, 1, bits)
    rho = (1+cosine_upper)/2
    if not 0 < rho < 1:
        raise ArithmeticError('spectral radius bound did not stay below one')
    tail = (Q(3*rank*2**(order-1), factorial(order-1)*(terms+1))
            *rho**(terms+1)/(1-rho))
    pi_lo, pi_hi = pi_interval(min(1024, bits+16))
    target = _outward((coefficient*pi_lo**(2*order), coefficient*pi_hi**(2*order)), bits+16)
    partial_bounds = _outward((partial, partial), bits+16)
    tail = _outward((Q(0), tail), bits+16)[1]
    lower, upper = partial_bounds[0], partial_bounds[1]+tail
    return dict(schema=schema, order=order, terms=terms,
                partial_interval=list(map(str, partial_bounds)), tail_absolute=str(tail), lower=str(lower),
                upper=str(upper), spectral_ratio_upper=str(rho),
                exact_pi_coefficient=str(coefficient), pi_power=2*order,
                target_interval=list(map(str, target)),
                independent_enclosure_overlap=lower <= target[1] and upper >= target[0],
                arithmetic='exact Fraction sum, outward dyadic bounds, Machin pi and cosine Taylor bounds',
                formal_kernel_verified=False)


def reflection_partial(order, terms=256, bits=64):
    """Positive rational inverse-binomial partial and an entire rational tail.

    If rho bounds cos²(pi/30), then Tr L^n <= 8*(4rho)^n. Together with
    e_r(n)<=2^r/r!, C(2n,n)>=4^n/(2n+1), this gives the explicit tail.
    The exact sum is rounded outward only for the small JSON coordinates.
    The claimed closed value is never used to construct the partial or tail.
    """
    _index(order, 1, MAX_ORDER, 'moment order')
    _index(terms, 0, MAX_TERMS, 'series terms')
    _index(bits, 8, 512, 'precision bits')
    coefficient = angle_moment_coefficient(e8_reflection_spectrum(), order)
    return _positive_series_enclosure(order, reflection_trace_sequence(terms), 8,
                                      coefficient, bits, 'pp-raghava-coxeter-partial/1')


def adjoint_trace_sequence(terms, *, deflate_trivial=False):
    """Actual adjoint traces of Lplus^n; optional removal of its eight 4 modes.

    Root-space signed cycles were conjugated to eight regular cycles by
    e8_lift.py. A cycle contributes 30 times the constant coefficient of
    (2+z+z^-1)^n modulo z^30-1. The Cartan part is the actual 8x8 recurrence.
    """
    _index(terms, 0, MAX_TERMS, 'trace terms')
    if type(deflate_trivial) is not bool:
        raise ValueError('deflate_trivial must be Boolean')
    reflection = reflection_trace_sequence(terms)
    coefficients = [1]+[0]*29
    answer = []
    for n in range(terms+1):
        answer.append(reflection[n]+240*coefficients[0]-(8*4**n if deflate_trivial else 0))
        coefficients = [2*coefficients[r]+coefficients[(r-1)%30]+coefficients[(r+1)%30]
                        for r in range(30)]
    return tuple(answer)


def adjoint_deflated_partial(order, terms=256, bits=64):
    """Positive, exponentially convergent adjoint series after exact endpoint removal.

    Sum e_(j-1)(n)*(Tr L_ad^n-8*4^n)/(n²*C(2n,n)) equals
    pi^(2j)*(r_j(adjoint)-8/(2j)!). For j=1 this is 112*pi²/3.
    Adding the removed eight arcsine endpoint values recovers the full
    adjoint moment 124*pi²/3 and hence its exact weight-two Mellin zero.
    """
    _index(order, 1, MAX_ORDER, 'moment order')
    _index(terms, 0, MAX_TERMS, 'series terms')
    _index(bits, 8, 512, 'precision bits')
    coefficient = angle_moment_coefficient(e8_adjoint_spectrum(), order)-Q(8, factorial(2*order))
    value = _positive_series_enclosure(order, adjoint_trace_sequence(terms, deflate_trivial=True),
                                       240, coefficient, bits, 'pp-raghava-coxeter-adjoint-partial/1')
    value.update(removed_trivial_dimension=8, removed_moment_pi_coefficient=str(Q(8, factorial(2*order))),
                 series_trace_coefficient='Tr(L_ad^n)-8*4^n')
    return value


def fixed_fiber_obstruction():
    """Natural restriction of the 240 primitive branches cannot be E8 root space."""
    fiber = root_fiber(1680, 264, primitive=True)
    restriction = fiber.restrict(30)
    e8_root_space = PhaseObject(30, tuple((q, 8) for q in range(30)))
    return dict(base_conductor=1680, extension_conductor=443520,
                primitive_fiber_dimension=int(fiber.dimension),
                restricted_terms=[[q, str(a)] for q, a in restriction.terms],
                e8_root_multiplicities=[8]*30,
                equivariant_isomorphism_possible=restriction == e8_root_space,
                reason='All fiber exponents are 1 modulo 30; the root Coxeter spectrum has every phase.')


def receipt(order=8):
    """Compact, deterministic exact coordinates for the derived commuting bridge."""
    _index(order, 1, MAX_ORDER, 'receipt moment order')
    reflection, adjoint = e8_reflection_spectrum(), e8_adjoint_spectrum()
    r = moment_vector(reflection, order)
    a = moment_vector(adjoint, order)
    z = mellin_from_moments(r)
    za = mellin_from_moments(a)
    if any(z[k] != even_period_coefficient(reflection, 2*k)
           or za[k] != even_period_coefficient(adjoint, 2*k) for k in range(1, order+1)):
        raise ArithmeticError('independent Bernoulli phase evaluation failed')
    degree = 264
    transfer = induction_moment_matrix(degree, order)
    transported = apply_matrix(transfer, a)
    bridge = bernoulli_bridge_matrix(order)
    diagonalized = tuple(tuple(bridge[j][k]*(Q(degree) if j == 0 else Q(1, degree**(2*j-1)))
                              for k in range(order+1)) for j in range(order+1))
    if matmul(bridge, transfer) != diagonalized:
        raise ArithmeticError('induction transfer was not diagonalized by the Bernoulli bridge')
    if matmul(transfer, induction_moment_matrix(2, order)) != induction_moment_matrix(2*degree, order):
        raise ArithmeticError('induction transfer failed its exact composition law')
    if moments_from_mellin(z) != r or moments_from_mellin(za) != a:
        raise ArithmeticError('the triangular Bernoulli inverse failed reconstruction')
    if transported[1]-transported[0]/6 != weight_two_defect(adjoint)/degree:
        raise ArithmeticError('induction failed the exact weight-two defect law')
    return dict(schema='pp-raghava-coxeter-unification/1', order=order,
                construction='One actual Coxeter operator, Raghava functional calculus, and the invertible Bernoulli transform',
                reflection_operator=reflection_operator_checks(),
                reflection_trace_prefix=list(reflection_trace_sequence(12)),
                reflection_series_enclosures=[reflection_partial(j, 128, 48) for j in range(1, min(3, order)+1)],
                reflection_precision_certificate=reflection_partial(1, 4096, 80),
                adjoint_endpoint_deflated_certificate=adjoint_deflated_partial(1, 2048, 80),
                reflection_moment_pi_coefficients=list(map(str, r)),
                reflection_mellin_pi_coefficients=list(map(str, z)),
                adjoint_moment_pi_coefficients=list(map(str, a)),
                adjoint_mellin_pi_coefficients=list(map(str, za)),
                bernoulli_bridge_matrix=[[str(x) for x in row] for row in bernoulli_bridge_matrix(order)],
                induction_264=dict(dimension=str(transported[0]),
                    first_moment_pi_squared_coefficient=str(transported[1]),
                    weight_two_defect=str(transported[1]-transported[0]/6),
                    bernoulli_diagonalization_checked=True, composition_with_degree_two_checked=True,
                    law='r1(Ind_d A)-dim(Ind_d A)/6 = (r1(A)-dim(A)/6)/d'),
                fixed_fiber_obstruction=fixed_fiber_obstruction(),
                sources=list(SOURCES),
                analytic_proof='scalar arcsine series plus spectral calculus; endpoint by monotone convergence; Bernoulli Fourier expansion and centered binomial theorem',
                analytic_formal_kernel_verified=False,
                novelty='derived bridge and concrete evaluations; historical originality not established')
