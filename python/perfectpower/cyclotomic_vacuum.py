"""Exact stationary-phase algebra and global minima of rational angular potentials.

An angular EFT construction is not a derivation of a particle-physics Lagrangian.
Polynomials and Sturm/energy enclosures are exact; angular labels are numerical.
"""
from fractions import Fraction as Q
from math import gcd
from . import polyalg as P
from .core import evaluate, mul, subtract


def cyclotomic_polynomial(order):
    if type(order) is not int or not 3 <= order <= 120:
        raise ValueError('integer order in 3..120 required')
    divisors = [d for d in range(1, order + 1) if order % d == 0]
    result = {}
    for d in divisors:
        a = P.poly([-1] + [0] * (d - 1) + [1])
        for e in divisors:
            if e < d and d % e == 0:
                a = P.exact_div(a, result[e])
        result[d] = a
    return result[order]


def cosine_polynomials(degree):
    """S_n(x)=z^n+z^-n=2cos(n theta), x=z+z^-1."""
    if type(degree) is not int or not 0 <= degree <= 120:
        raise ValueError('degree in 0..120 required')
    out = [P.poly([2]), P.X]
    for _ in range(2, degree + 1):
        out.append(subtract(mul(P.X, out[-1]), out[-2]))
    return out[:degree + 1]


def real_cyclotomic_polynomial(order):
    """Psi_n with Phi_n(z)=z^(phi(n)/2) Psi_n(z+z^-1)."""
    a = cyclotomic_polynomial(order)
    m = P.degree(a) // 2
    if a != a[::-1]:
        raise AssertionError('reciprocity failed')
    ss = cosine_polynomials(m)
    out = P.poly([a[m]])
    for j in range(1, m + 1):
        out = P.add(out, P.scale(ss[j], a[m + j]))
    return out


def phase_potential(order, multiplier=(1,)):
    """V'(x)=Psi_order(x)*multiplier(x), x=2cos(theta); V(0)=0.

    Fraction/string/integer coefficients only. Every primitive order-th-root
    angle is stationary; selecting the multiplier remains model construction.
    """
    if any(isinstance(v, (float, bool)) for v in multiplier):
        raise ValueError('exact rational multiplier required')
    q = P.poly(map(Q, multiplier))
    if P.is_zero(q) or P.degree(q) > 6:
        raise ValueError('nonzero multiplier of degree at most six required')
    derivative = mul(real_cyclotomic_polynomial(order), q)
    return P.poly([0] + [a / (i + 1) for i, a in enumerate(derivative)])


def fourier_coefficients(potential):
    """Exact coefficients v_n in V(2cos theta)=sum v_n*cos(n theta)."""
    v = P.poly(potential)
    ss = cosine_polynomials(P.degree(v))
    out = [Q(0)] * len(v)
    for j in range(P.degree(v), 0, -1):
        c = v[j] if j < len(v) else Q(0)
        out[j] = 2 * c
        v = subtract(v, P.scale(ss[j], c))
    out[0] = v[0]
    return tuple(out)


def rational_rank(rows):
    a = [list(map(Q, row)) for row in rows]
    if not a:
        return 0
    rank = 0
    for col in range(len(a[0])):
        pivot = next((j for j in range(rank, len(a)) if a[j][col]), None)
        if pivot is None:
            continue
        a[rank], a[pivot] = a[pivot], a[rank]
        t = a[rank][col]
        a[rank] = [v / t for v in a[rank]]
        for j in range(len(a)):
            if j != rank:
                t = a[j][col]
                a[j] = [u - t * v for u, v in zip(a[j], a[rank])]
        rank += 1
        if rank == len(a):
            break
    return rank


def stationary_coupling_constraints(order, harmonics, active_harmonics=None):
    """Linear rational relations needed for exact stationarity at primitive phase.

    Nonconstant cosine terms are the coordinates; stationarity is derivative
    divisibility by the real cyclotomic minimal polynomial. No CP-odd terms.
    """
    if type(harmonics) is not int or not 1 <= harmonics <= 30:
        raise ValueError('harmonics in 1..30 required')
    active = list(range(1, harmonics + 1)) if active_harmonics is None else list(active_harmonics)
    if not active or len(active) != len(set(active)) or any(type(j) is not int or not 1 <= j <= harmonics for j in active):
        raise ValueError('distinct active harmonics in declared range required')
    p = real_cyclotomic_polynomial(order)
    ss = cosine_polynomials(harmonics)
    columns = [P.divmod_poly(P.scale(P.derivative(ss[j]), Q(1, 2)), p)[1]
               for j in active]
    rows = [[a[i] if i < len(a) else Q(0) for a in columns] for i in range(P.degree(p))]
    rank = rational_rank(rows)
    return {'order': order, 'harmonics': harmonics, 'active_harmonics': active, 'rational_constraints': rank,
            'stationary_family_dimension': len(active) - rank,
            'matrix': [[str(v) for v in row] for row in rows]}


def _variations(chain, point):
    signs = [evaluate(p, point) > 0 for p in chain if evaluate(p, point) != 0]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def isolate_real_roots(polynomial, lo=Q(-2), hi=Q(2), bits=70):
    """All distinct roots in (lo,hi], rational Sturm bisection enclosures.

    Endpoints which are roots obey the Sturm half-open convention. Use a
    separate endpoint candidate when optimizing on a closed interval.
    """
    if type(bits) is not int or not 12 <= bits <= 160 or lo >= hi:
        raise ValueError('invalid root isolation domain')
    p = P.poly(polynomial)
    if P.is_zero(p):
        raise ValueError('zero polynomial has no finite root list')
    if P.degree(p) == 0:
        return []
    sq = P.exact_div(p, P.gcd_poly(p, P.derivative(p)))
    chain = P.sturm_chain(sq)
    width = Q(1, 2 ** bits)
    stack = [(Q(lo), Q(hi))]
    out = []
    while stack:
        a, b = stack.pop()
        n = _variations(chain, a) - _variations(chain, b)
        if not n:
            continue
        if n == 1 and b - a <= width:
            out.append((a, b))
            continue
        mid = (a + b) / 2
        stack.extend([(mid, b), (a, mid)])
    return sorted(out)


def interval_evaluate(polynomial, interval):
    """Rational Horner enclosure, without a floating-point root substitution."""
    lo, hi = map(Q, interval)
    if lo > hi:
        raise ValueError('ordered interval required')
    a = b = Q(0)
    for c in reversed(polynomial):
        products = (a * lo, a * hi, b * lo, b * hi)
        a, b = min(products) + c, max(products) + c
    return a, b


def certify_global_minimum(potential, bits=70):
    """Compare every stationary root and both endpoints of x in [-2,2].

    A unique winner is exact when its energy upper bound is below all other
    lower bounds. Ties/insufficient separation are returned as unresolved;
    this function never quietly selects one of them.
    """
    v = P.poly(potential)
    if P.degree(v) < 1:
        raise ValueError('nonconstant potential required')
    d = P.derivative(v)
    interior = isolate_real_roots(d, bits=bits)
    if evaluate(d, Q(2)) == 0:
        # The closed-domain endpoint is already represented exactly below.
        interior = [r for r in interior if r[1] != 2]
    intervals = [(Q(-2), Q(-2))] + interior + [(Q(2), Q(2))]
    energies = [interval_evaluate(v, r) for r in intervals]
    best_upper = min(b for a, b in energies)
    eligible = [i for i, (a, b) in enumerate(energies) if a <= best_upper]
    winner = eligible[0] if len(eligible) == 1 else None
    gap = None if winner is None else min(a for i, (a, b) in enumerate(energies) if i != winner) - energies[winner][1]
    return {'status': 'unique_global_minimum_in_x' if winner is not None else 'ties_or_unresolved_enclosures',
            'winner_index': winner, 'eligible_indices': eligible,
            'critical_points': [{'x_interval': list(map(str, r)), 'energy_interval': list(map(str, e))}
                                for r, e in zip(intervals, energies)],
            'energy_gap_lower_bound': None if gap is None else str(gap),
            'bits': bits, 'scope': 'exact rational Sturm counts and interval energy comparison; no Lean theorem'}


def golden_portal_identity():
    """Reduce C=1-2cos(12 theta) in the real Phi60 carrier."""
    p = real_cyclotomic_polynomial(60)
    c = subtract(P.ONE, cosine_polynomials(12)[12])
    c = P.divmod_poly(c, p)[1]
    residual = P.divmod_poly(P.add(subtract(mul(c, c), P.scale(c, 3)), P.ONE), p)[1]
    return {'real_modulus': list(map(str, p)), 'coefficient_polynomial': list(map(str, c)),
            'golden_identity_remainder': list(map(str, residual))}
