"""Integral Descartes reflections and polynomial parabolic curvature orbits."""
from fractions import Fraction as Q
from .core import integer_power_root
from .recurrence import Recurrence


def quadruple(values):
    values = tuple(values)
    if len(values) != 4 or any(type(x) is not int for x in values):
        raise ValueError('four integer signed curvatures required')
    if sum(values) ** 2 != 2 * sum(x*x for x in values):
        raise ValueError('curvatures do not satisfy Descartes equation')
    return values


def reflect(values, index):
    values = quadruple(values)
    if type(index) is not int or not 0 <= index < 4:
        raise ValueError('reflection index must be 0..3')
    out = list(values)
    out[index] = 2 * (sum(values) - values[index]) - values[index]
    return quadruple(out)


def parabolic_family(values=(-1, 2, 2, 3), fixed=(0, 1)):
    values = quadruple(values)
    fixed = tuple(fixed)
    if len(fixed) != 2 or len(set(fixed)) != 2 or any(type(i) is not int or not 0 <= i < 4 for i in fixed):
        raise ValueError('two distinct fixed circle indices required')
    moving = [i for i in range(4) if i not in fixed]
    u, v = [values[i] for i in moving]
    s = sum(values[i] for i in fixed)
    coefficients = (u, v-u-s, s)
    # Homogeneous annihilator (E-1)^3, exactly compatible with existing recurrence code.
    rec = Recurrence((1, -3, 3), (u, v, 2*s+2*v-u))
    return {'schema': 'pp-descartes-family/1', 'seed': list(values), 'fixed_indices': list(fixed),
            'moving_indices': moving, 'fixed_sum': s, 'polynomial': list(coefficients),
            'inhomogeneous_recurrence': {'constant': 2*s, 'coefficients': [-1, 2]},
            'homogeneous_recurrence': {'coefficients': [1, -3, 3], 'initial': list(map(int, rec.initial))},
            'formalized': False, 'scope': 'algebraic integral Descartes orbit; geometric packing admissibility is separate'}


def orbit_packet(values=(-1, 2, 2, 3), fixed=(0, 1), stop=1000, powers=(2, 3, 4)):
    if type(stop) is not int or not 0 <= stop <= 1_000_000:
        raise ValueError('exclusive stop must be 0..1000000')
    powers = tuple(powers)
    if not powers or any(type(d) is not int or not 2 <= d <= 64 for d in powers):
        raise ValueError('powers must be integers 2..64')
    family = parabolic_family(values, fixed)
    u, linear, s = family['polynomial']
    state = quadruple(values)
    moving = family['moving_indices']
    hits = {str(d): [] for d in powers}
    prefix = []
    for n in range(stop):
        b = u + linear*n + s*n*n
        if n < 2:
            actual = state[moving[n]]
        else:
            state = reflect(state, moving[n % 2])
            actual = state[moving[n % 2]]
        if actual != b:
            raise AssertionError('reflection orbit disagrees with polynomial')
        if n < 32:
            prefix.append(b)
        for d in powers:
            root = integer_power_root(b, d)
            if root is not None:
                hits[str(d)].append({'index': n, 'curvature': b, 'root': root})
    return {**family, 'stop_exclusive': stop, 'prefix': prefix, 'hits': hits,
            'enumeration_scope': 'bounded scan only', 'complete_hit_classification': False,
            'checked_identity': 'every generated curvature equals the supplied quadratic polynomial'}
