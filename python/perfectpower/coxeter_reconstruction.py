"""Finite positive spectral certificates and exact odd-Mellin orientation.

This is standard univariate Hankel/Prony mathematics specialized to the
actual Raghava--Coxeter bridge. No lattice, Lie bracket, historical priority,
or Lean-kernel reconstruction is inferred from spectral identifiability.
"""
from fractions import Fraction as Q
from math import factorial, isqrt, lcm

from .e8_periods import bernoulli_polynomial
from .period_transport import PhaseObject
from .raghava_coxeter import e8_reflection_spectrum, e8_adjoint_spectrum

MAX_ORDER = 64
SOURCES = ('https://arxiv.org/abs/0812.2563', 'https://dlmf.nist.gov/24.8.E2')


def _q(value):
    if type(value) not in (int, Q, str):
        raise ValueError('exact integer, Fraction or rational string required')
    return Q(value)


def _order(n):
    if type(n) is not int or not 0 <= n <= MAX_ORDER:
        raise ValueError('order must be an integer from zero through 64')
    return n


def _solve(a, b):
    n = len(b)
    if len(a) != n or any(len(row) != n for row in a):
        raise ValueError('square exact system required')
    rows = [[Q(x) for x in row]+[Q(y)] for row, y in zip(a, b)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if rows[i][j]), None)
        if pivot is None:
            raise ValueError('singular exact moment system')
        rows[j], rows[pivot] = rows[pivot], rows[j]
        scale = rows[j][j]
        rows[j] = [x/scale for x in rows[j]]
        for i in range(n):
            if i != j:
                factor = rows[i][j]
                rows[i] = [x-factor*y for x, y in zip(rows[i], rows[j])]
    return tuple(row[-1] for row in rows)


def _determinant(a):
    a = [list(map(Q, row)) for row in a]
    result = Q(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return Q(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            result = -result
        value = a[j][j]
        result *= value
        for i in range(j+1, len(a)):
            factor = a[i][j]/value
            for k in range(j+1, len(a)):
                a[i][k] -= factor*a[j][k]
    return result


def _evaluate(coefficients, x):
    value = Q(0)
    for c in reversed(coefficients):
        value = value*x+c
    return value


def _sqrt(value):
    a, b = isqrt(value.numerator), isqrt(value.denominator)
    if a*a != value.numerator or b*b != value.denominator:
        raise ValueError('the executable phase inverse requires rational-square nodes')
    return Q(a, b)


def folded_profile(spectrum, *, positive=True):
    if not isinstance(spectrum, PhaseObject):
        raise ValueError('PhaseObject required')
    if positive and (not spectrum.terms or any(w < 0 for _, w in spectrum.terms)):
        raise ValueError('a nonempty nonnegative phase profile is required')
    data = {}
    for q, w in spectrum.phases():
        x = (q-Q(1, 2))**2
        data[x] = data.get(x, Q(0))+w
    return tuple(sorted((x, w) for x, w in data.items() if w))


def power_moments(spectrum, order):
    _order(order)
    profile = folded_profile(spectrum, positive=False)
    return tuple(sum((w*x**j for x, w in profile), Q(0)) for j in range(order+1))


def power_from_raghava(values):
    values = tuple(map(_q, values))
    _order(len(values)-1)
    return tuple(factorial(2*j)*v/Q(4**j) for j, v in enumerate(values))


def annihilator_from_moments(moments, atoms):
    """Recover p(X) monic degree s from mu_0,...,mu_(2s-1)."""
    if type(atoms) is not int or not 1 <= atoms <= 32:
        raise ValueError('one through 32 atoms required')
    moments = tuple(map(_q, moments))
    if len(moments) < 2*atoms:
        raise ValueError('2s moments are required')
    h = tuple(tuple(moments[i+j] for j in range(atoms)) for i in range(atoms))
    p = _solve(h, tuple(-moments[atoms+i] for i in range(atoms)))
    return p+(Q(1),)


def positive_certificate(moments, nodes):
    """Check rational candidate roots and the global positive uniqueness proof.

    Providing candidate roots is an extraction convenience. The annihilator
    itself is recovered from moments, and the extra square identity proves
    uniqueness against arbitrary real positive finite competitors.
    """
    moments, nodes = tuple(map(_q, moments)), tuple(map(_q, nodes))
    s = len(nodes)
    if not s or len(set(nodes)) != s or any(x < 0 or x > Q(1, 4) for x in nodes):
        raise ValueError('distinct folded nodes in [0,1/4] required')
    if len(moments) != 2*s+1:
        raise ValueError('exactly 2s+1 moments required for the positive certificate')
    nodes = tuple(sorted(nodes))
    p = annihilator_from_moments(moments, s)
    if any(_evaluate(p, x) for x in nodes):
        raise ValueError('candidate nodes do not exhaust the recovered annihilator')
    weights = _solve(tuple(tuple(x**i for x in nodes) for i in range(s)), moments[:s])
    if any(w <= 0 for w in weights):
        raise ValueError('strictly positive support weights required')
    if any(sum(w*x**j for x, w in zip(nodes, weights)) != m for j, m in enumerate(moments)):
        raise ValueError('support does not reproduce the supplied moments')
    square = sum(p[i]*p[j]*moments[i+j] for i in range(s+1) for j in range(s+1))
    if square:
        raise ValueError('positive annihilator-square certificate failed')
    h = tuple(tuple(moments[i+j] for j in range(s)) for i in range(s))
    determinant = _determinant(h)
    if determinant <= 0:
        raise ValueError('positive Hankel determinant required')
    return dict(nodes=nodes, weights=weights, annihilator=p,
                hankel_determinant=determinant, square_integral=square,
                sufficient_coordinates=2*s+1, uniqueness_scope='all nonnegative finite phase profiles; no conductor or support bound')


def predict_moments(initial, annihilator, count):
    _order(count)
    p, initial = tuple(map(_q, annihilator)), tuple(map(_q, initial))
    s = len(p)-1
    if s < 1 or p[-1] != 1 or len(initial) < s:
        raise ValueError('monic positive-degree annihilator and initial moments required')
    result = list(initial[:min(len(initial), count+1)])
    while len(result) <= count:
        n = len(result)-s
        result.append(-sum(p[i]*result[n+i] for i in range(s)))
    return tuple(result)


def _phase_object(phases):
    conductor = 1
    for q, _ in phases:
        conductor = lcm(conductor, q.denominator)
    return PhaseObject(conductor, tuple((int(q*conductor), w) for q, w in phases))


def symmetric_profile(nodes, weights):
    phases = []
    for x, w in zip(map(_q, nodes), map(_q, weights)):
        if not 0 <= x <= Q(1, 4):
            raise ValueError('folded node outside [0,1/4]')
        if x == 0:
            phases.append((Q(1, 2), w))
        elif x == Q(1, 4):
            phases.append((Q(0), w))
        else:
            t = _sqrt(x)
            phases.extend(((Q(1, 2)-t, w/2), (Q(1, 2)+t, w/2)))
    return _phase_object(phases)


def odd_mellin_coefficients(spectrum, count):
    _order(count)
    if not isinstance(spectrum, PhaseObject):
        raise ValueError('PhaseObject required')
    return tuple(Q((-1)**(k+1)*2**(2*k), factorial(2*k+1))*sum(
        (w*bernoulli_polynomial(2*k+1, q) for q, w in spectrum.phases()), Q(0))
        for k in range(1, count+1))


def recover_orientation(nodes, weights, odd):
    nodes, weights, odd = tuple(map(_q, nodes)), tuple(map(_q, weights)), tuple(map(_q, odd))
    if len(nodes) != len(weights) or len(set(nodes)) != len(nodes) or any(w <= 0 for w in weights):
        raise ValueError('distinct nodes and positive weights required')
    if any(x < 0 or x > Q(1, 4) for x in nodes):
        raise ValueError('folded node outside [0,1/4]')
    interior = [i for i, x in enumerate(nodes) if 0 < x < Q(1, 4)]
    if len(odd) != len(interior):
        raise ValueError('one odd coordinate for each interior folded node required')
    ts = [_sqrt(nodes[i]) for i in interior]
    rows = tuple(tuple(Q((-1)**(k+1)*2**(2*k), factorial(2*k+1))*bernoulli_polynomial(2*k+1, Q(1, 2)+t)
                       for t in ts) for k in range(1, len(interior)+1))
    differences = _solve(rows, odd) if interior else ()
    phase_rows = []
    diffs = dict(zip(interior, differences))
    for i, (x, w) in enumerate(zip(nodes, weights)):
        if x == 0:
            phase_rows.append((Q(1, 2), w))
        elif x == Q(1, 4):
            phase_rows.append((Q(0), w))
        else:
            t, difference = _sqrt(x), diffs[i]
            minus, plus = (w-difference)/2, (w+difference)/2
            if minus < 0 or plus < 0:
                raise ValueError('odd observations require a negative phase weight')
            phase_rows.extend(((Q(1, 2)-t, minus), (Q(1, 2)+t, plus)))
    return _phase_object(phase_rows)


def sharpness_witness():
    nodes = tuple(map(Q, ('0', '1/225', '1/100', '4/225', '1/25', '16/225', '1/9', '49/225', '1/4')))
    delta = []
    for i, x in enumerate(nodes):
        denominator = Q(1)
        for j, y in enumerate(nodes):
            if i != j:
                denominator *= x-y
        delta.append(1/denominator)
    epsilon = min(1/(-delta[i]) for i in (1, 3, 5, 7))
    weights = tuple(2*int(i % 2 == 1)+epsilon*d for i, d in enumerate(delta))
    alternative = symmetric_profile(nodes, weights)
    old, new = power_moments(e8_reflection_spectrum(), 8), power_moments(alternative, 8)
    if any(w <= 0 for w in weights) or old[:8] != new[:8] or new[8]-old[8] != epsilon:
        raise ArithmeticError('positive rational sharpness certificate failed')
    if any(sum(d*x**k for d, x in zip(delta, nodes)) != int(k == 8) for k in range(9)):
        raise ArithmeticError('Lagrange divided-difference identity failed')
    return dict(nodes=nodes, weights=weights, epsilon=epsilon, profile=alternative,
                matching_coordinates=8, first_difference_order=8,
                integer_dimension_eight_minimality_claimed=False)


def _serialize(value):
    if isinstance(value, Q):
        return str(value)
    if isinstance(value, PhaseObject):
        return value.packet()
    if isinstance(value, dict):
        return {k: _serialize(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [_serialize(x) for x in value]
    return value


def receipt():
    result = dict(schema='pp-coxeter-finite-reconstruction/1', sources=list(SOURCES),
                  formal_kernel_verified=False, novelty='derived application of classical positive moment and Bernoulli theory; historical priority not established')
    for name, spectrum in (('reflection', e8_reflection_spectrum()), ('adjoint', e8_adjoint_spectrum())):
        profile = folded_profile(spectrum)
        nodes, weights = zip(*profile)
        cert = positive_certificate(power_moments(spectrum, 2*len(nodes)), nodes)
        odd_count = sum(0 < x < Q(1, 4) for x in nodes)
        odd = odd_mellin_coefficients(spectrum, odd_count)
        recovered = recover_orientation(nodes, weights, odd)
        if recovered.lift(spectrum.conductor) != spectrum:
            raise ArithmeticError('oriented spectrum reconstruction failed')
        cert.update(odd_coordinates=odd_count, odd_coefficients=odd, oriented_reconstruction_checked=True)
        result[name] = cert
    result['adjoint_odd_coordinates'] = result['adjoint']['odd_coordinates']
    result['sharpness'] = sharpness_witness()
    return _serialize(result)
