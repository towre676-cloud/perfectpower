"""Mechanism diagnostics for a golden-coefficient CKM hypothesis.

Finite symmetry and integer-matrix censuses are exact. A constructed angular
potential is a conditional EFT, not an independently discovered UV theory.
"""
from fractions import Fraction
from itertools import permutations, product
from math import gcd, lcm, factorial
from collections import Counter
import heapq


def signed_permutation_order(permutation, signs):
    n = len(permutation)
    if sorted(permutation) != list(range(n)) or len(signs) != n or any(s not in (-1, 1) for s in signs):
        raise ValueError('signed permutation required')
    visited = set()
    order = 1
    for i in range(n):
        if i in visited:
            continue
        j, size, parity = i, 0, 1
        while j not in visited:
            visited.add(j)
            size += 1
            parity *= signs[j]
            j = permutation[j]
        order = lcm(order, size if parity == 1 else 2 * size)
    return order


def weyl_order_census(dimension=5):
    if type(dimension) is not int or not 1 <= dimension <= 6:
        raise ValueError('dimension in 1..6 required for exhaustive census')
    counts = Counter(signed_permutation_order(p, s)
                     for p in permutations(range(dimension))
                     for s in product((-1, 1), repeat=dimension))
    if sum(counts.values()) != 2 ** dimension * factorial(dimension):
        raise AssertionError('group census incomplete')
    return {'dimension': dimension, 'group_order': sum(counts.values()),
            'element_order_counts': {str(k): counts[k] for k in sorted(counts)},
            'contains_order60': 60 in counts,
            'scope': 'single-element order / primitive eigenphase obstruction, not a prohibition on all composite flavor models'}


def minimum_signed_dimension(target=60):
    """Shortest lcm cover of target by signed cycle orders, exact finite DP."""
    if type(target) is not int or not 2 <= target <= 120:
        raise ValueError('target in 2..120 required')
    options = [(n, parity, n if parity == 1 else 2 * n)
               for n in range(1, target + 1) for parity in (1, -1)
               if target % (n if parity == 1 else 2 * n) == 0]
    queue = [(0, 1, ())]; best = {1: 0}
    while queue:
        cost, order, path = heapq.heappop(queue)
        if cost != best[order]:
            continue
        if order == target:
            return {'target_order': target, 'minimum_dimension': cost,
                    'signed_cycles': [{'length': n, 'sign_product': p, 'order': o} for n, p, o in path]}
        for n, parity, cycle_order in options:
            new_order = lcm(order, cycle_order); new_cost = cost + n
            if new_cost < best.get(new_order, target + 1):
                best[new_order] = new_cost
                heapq.heappush(queue, (new_cost, new_order, path + ((n, parity, cycle_order),)))
    raise AssertionError('lcm cover missing')


def integer_transfer_census(bound=12):
    """Positive integral symmetric determinant-one 2x2 matrices; no float filter.

    For nonidentity matrices trace T>=3, hence lambda_- <= (3-sqrt(5))/2.
    The extremum is trace three. Matrix basis/portal identification are physical
    assumptions; an integral matrix can be changed by nonorthogonal basis maps.
    """
    if type(bound) is not int or not 2 <= bound <= 100:
        raise ValueError('integer bound in 2..100 required')
    rows = []
    for a, d in product(range(1, bound + 1), repeat=2):
        for b in range(-bound, bound + 1):
            if a * d - b * b == 1:
                rows.append({'matrix': [[a, b], [b, d]], 'trace': a + d,
                             'characteristic_polynomial': [1, -a - d, 1]})
    nontrivial = [r for r in rows if r['trace'] > 2]
    return {'bound': bound, 'count': len(rows), 'trace_counts': dict(sorted(Counter(r['trace'] for r in rows).items())),
            'minimal_nontrivial_trace': min(r['trace'] for r in nontrivial),
            'extremizers': [r for r in nontrivial if r['trace'] == 3],
            'rows': rows, 'unbounded_argument': 'trace is an integer >=2; trace=2 forces identity; smaller eigenvalue decreases with trace',
            'scope': 'conditional spectral minimality, not a symmetry derivation of kinetic normalization or a Yukawa portal'}


def numerical_minima(potential):
    """All stationary candidates and endpoints; numerical labels only."""
    import numpy as np
    from . import polyalg as P
    v = np.array(list(map(float, potential)))
    d = np.array(list(map(float, P.derivative(potential))))
    roots = np.polynomial.polynomial.polyroots(d)
    xs = [-2., 2.] + [float(r.real) for r in roots if abs(r.imag) < 1e-7 and -2 < r.real < 2]
    xs = np.array(sorted(xs))
    energies = np.polynomial.polynomial.polyval(xs, v)
    ix = np.flatnonzero(energies <= energies.min() + 1e-8)
    return {'angles': [float(np.degrees(np.arccos(xs[i] / 2))) for i in ix],
            'x': [float(xs[i]) for i in ix], 'energy': float(energies.min())}


def selector_census(bound=3):
    """Every primitive integer multiplier of degree <=3 in a symmetric box.

    Returns all selected phases without taking a desired target as input.
    Search classifications are numerical; headline constructions get a separate
    exact global-minimum certificate. Opposite signs are distinct potentials.
    """
    from .cyclotomic_vacuum import phase_potential
    if type(bound) is not int or not 1 <= bound <= 5:
        raise ValueError('bound in 1..5 required')
    records = []
    counts = Counter()
    for coefficients in product(range(-bound, bound + 1), repeat=4):
        if not any(coefficients) or gcd(*coefficients) != 1:
            continue
        v = phase_potential(60, coefficients)
        result = numerical_minima(v)
        key = ','.join(f'{a:.6f}' for a in sorted(result['angles']))
        counts[key] += 1
        records.append({'multiplier': list(coefficients), 'l1': sum(abs(c) for c in coefficients), **result})
    return {'bound': bound, 'primitive_multiplier_count': len(records),
            'minimum_angle_counts': dict(sorted(counts.items())), 'records': records,
            'scope': 'exhaustive declared integer box; numerical stationary-root comparison; target-aware model construction remains retrospective'}


def vacuum_predictions(potential, vus, vcb):
    """CKM consequences of a constructed minimum and its cyclotomic portal."""
    import numpy as np
    from .flavor_prediction import ckm_from_depth, observables
    minima = numerical_minima(potential)
    out = []
    for degrees in minima['angles']:
        theta = np.radians(degrees)
        coefficient = 1 - 2 * np.cos(12 * theta)
        if not 0 <= coefficient <= 2:
            out.append({'phase_degrees': degrees, 'coefficient': float(coefficient), 'physical_chart': False})
            continue
        V = ckm_from_depth(coefficient, theta, vus, vcb)
        obs = {k: float(v) for k, v in observables(V).items()}
        beta = np.angle(-V[1, 0] * V[1, 2].conj() / (V[2, 0] * V[2, 2].conj()))
        obs.update({'beta': float(np.degrees(beta)), 'alpha_triangle': 180 - float(np.degrees(beta)) - obs['gamma']})
        out.append({'phase_degrees': degrees, 'coefficient': float(coefficient), 'physical_chart': True, 'predictions': obs})
    return out


def yukawa_embedding(V, up_spectrum, down_spectrum):
    """Existence embedding Yu=diag(yu), Yd=V diag(yd), positive spectra.

    Does not derive masses, enforce UV charges, protect theta_bar, or perform RG.
    """
    import numpy as np
    u, d = np.asarray(up_spectrum, dtype=float), np.asarray(down_spectrum, dtype=float)
    V = np.asarray(V, dtype=complex)
    if V.shape != (3, 3) or u.shape != (3,) or d.shape != (3,) or np.any(u <= 0) or np.any(d <= 0) or not np.all(np.isfinite(u)) or not np.all(np.isfinite(d)):
        raise ValueError('unitary 3x3 matrix and positive finite spectra required')
    if not np.all(np.isfinite(V)) or np.max(np.abs(V @ V.conj().T - np.eye(3))) > 1e-10:
        raise ValueError('unitary matrix required')
    return np.diag(u), V @ np.diag(d)


def cyclotomic_portal_polynomial(vus_squared, vcb_squared, vub_squared, vtd_squared):
    """Exact polynomial eliminant in four rephasing-invariant squared magnitudes.

    U*V*H^2 - W*(1-W)^2*B^12, where H=B^6 F(A/B),
    F(q)=1-2cos(12theta) expressed in q=cos(theta)^2.
    This polynomial necessary condition has extra sign/phase branches; physical
    CKM compatibility, positive C, and vacuum selection must be retained.
    """
    values = (vus_squared, vcb_squared, vub_squared, vtd_squared)
    if any(isinstance(v, (float, bool)) for v in values):
        raise ValueError('exact rational squared magnitudes required')
    u, v, w, d = map(Fraction, values); s = 1 - w
    if not (0 < w < 1 and 0 < u < s and 0 < v < s and 0 <= d <= 1):
        raise ValueError('nondegenerate squared-magnitude chart required')
    n = u*v + w*(s-u)*(s-v) - d*s*s
    a = n*n; b = 4*u*v*(s-u)*(s-v)*w
    f = (-1, 144, -1680, 7168, -13824, 12288, -4096)
    h = sum(c*a**i*b**(6-i) for i, c in enumerate(f))
    return u*v*h*h - w*s*s*b**12


def portal_diagnostic(V):
    """Numerical, rephasing-invariant residual from CKM magnitudes alone."""
    import numpy as np
    V = np.asarray(V, dtype=complex)
    if V.shape != (3, 3) or not np.all(np.isfinite(V)) or np.max(np.abs(V @ V.conj().T - np.eye(3))) > 1e-10:
        raise ValueError('unitary 3x3 matrix required')
    u, v, w, d = float(abs(V[0, 1])**2), float(abs(V[1, 2])**2), float(abs(V[0, 2])**2), float(abs(V[2, 0])**2)
    s = 1-w; n = u*v+w*(s-u)*(s-v)-d*s*s; b = 4*u*v*(s-u)*(s-v)*w
    if b <= 0:
        raise ValueError('nondegenerate chart required')
    q = n*n/b
    expected = float(np.polynomial.polynomial.polyval(q, (-1, 144, -1680, 7168, -13824, 12288, -4096)))
    actual = np.sqrt(w)*s/np.sqrt(u*v)
    return {'cos_delta_squared': q, 'depth_from_magnitudes': float(actual),
            'depth_from_phase_portal': expected, 'normalized_portal_residual': float(actual-expected),
            'scope': 'necessary portal relation; CP sign and chosen vacuum not inferred from even phase harmonics'}


def angular_response(potential):
    """Local response to independent CP-even Fourier perturbations."""
    import numpy as np
    from . import polyalg as P
    from .cyclotomic_vacuum import fourier_coefficients
    phases = numerical_minima(potential)['angles']
    if len(phases) != 1:
        raise ValueError('unique minimum in 0..pi required')
    theta = np.radians(phases[0]); x = 2 * np.cos(theta)
    curvature = 4 * np.sin(theta) ** 2 * float(np.polynomial.polynomial.polyval(x, list(map(float, P.derivative(P.derivative(potential))))))
    fprime = 24 * np.sin(12 * theta)
    coefficients = fourier_coefficients(potential)
    response = [n * np.sin(n * theta) / curvature for n in range(1, len(coefficients))]
    return {'phase_degrees': phases[0], 'angular_curvature': float(curvature),
            'coefficient_derivative_per_radian': float(fprime),
            'dtheta_depsilon_radians': list(map(float, response)),
            'dC_depsilon': [float(fprime * r) for r in response],
            'fourier_coefficients': list(map(str, coefficients)),
            'scope': 'linear response to epsilon*cos(n theta), angular EFT normalization fixed; not scalar masses'}


def vacuum_occupation(potential, grid=65536):
    """Gradient attraction basins and illustrative canonical Gibbs occupation.

    Uniform angular initial conditions and canonical angular measure are stated
    assumptions. Dimensionless temperatures do not assert a cosmological scale
    or a cooling history. CP partner occupations are identical.
    """
    import numpy as np
    from . import polyalg as P
    from .cyclotomic_vacuum import fourier_coefficients, certify_global_minimum
    cert = certify_global_minimum(potential, bits=48)
    labels = []
    second = np.array(list(map(float, P.derivative(P.derivative(potential)))))
    for record in cert['critical_points'][1:-1]:
        a, b = map(Fraction, record['x_interval']); x = float((a + b) / 2)
        theta = np.arccos(x / 2)
        curvature = 4 * np.sin(theta)**2 * np.polynomial.polynomial.polyval(x, second)
        labels.append((float(theta), float(curvature)))
    maxima = sorted(t for t, curvature in labels if curvature < 0)
    boundaries = [0.] + maxima + [float(np.pi)]
    minima = sorted(t for t, curvature in labels if curvature > 0)
    basins = []
    for a, b in zip(boundaries, boundaries[1:]):
        hits = [t for t in minima if a < t < b]
        if not hits:
            hits = [0. if a == 0 else float(np.pi)]
        if len(hits) != 1:
            raise AssertionError('non-Morse basin or missing critical point')
        basins.append({'minimum_degrees': float(np.degrees(hits[0])),
                       'basin_degrees': [float(np.degrees(a)), float(np.degrees(b))],
                       'uniform_initial_fraction': float((b - a) / np.pi)})
    theta = (np.arange(grid) + .5) * np.pi / grid
    f = np.array(list(map(float, fourier_coefficients(potential))))
    energy = np.cos(theta[:, None] * np.arange(len(f))[None, :]) @ f
    studies = []
    for temperature in (.1, .05, .02, .01):
        weights = np.exp(-(energy - energy.min()) / temperature); weights /= weights.sum()
        occupation = [float(weights[(theta >= a) & (theta < b)].sum()) for a, b in zip(boundaries, boundaries[1:])]
        studies.append({'dimensionless_temperature': temperature, 'basin_probabilities': occupation})
    return {'grid': grid, 'gradient_basins_positive_half_circle': basins, 'Gibbs_positive_half_circle': studies,
            'CP_partner_probability_ratio': 1.,
            'scope': 'conditional dynamics/occupation examples; no derived cosmological temperature, tunneling rate or vacuum history'}


def _fourier_global_minimum(coefficients):
    """Numerical global angular minimum from the Laurent stationary equation.

    z^N sum n*v_n*(z^n-z^-n)=0; retain all unit-circle roots and endpoints.
    """
    import numpy as np
    c = np.asarray(coefficients, dtype=float)
    degree = len(c) - 1
    p = np.zeros(2 * degree + 1)
    for n in range(1, degree + 1):
        p[degree + n] += n * c[n]
        p[degree - n] -= n * c[n]
    roots = np.polynomial.polynomial.polyroots(p)
    phases = [0., np.pi]
    phases.extend(float(np.angle(z)) for z in roots if abs(abs(z) - 1) < 1e-6 and 0 < np.angle(z) < np.pi)
    phases = np.asarray(phases)
    values = np.cos(phases[:, None] * np.arange(len(c))[None, :]) @ c
    return float(phases[np.argmin(values)])


def perturbation_study(potential, vus, vcb, samples=2048, seed=6052026):
    """Declared coupling-noise scenarios, not a posterior over physical theories.

    Generic perturbations affect each nonconstant Fourier coordinate equally in
    RMS. Structured perturbations keep the common cyclotomic derivative factor.
    """
    import numpy as np
    from . import polyalg as P
    from .cyclotomic_vacuum import fourier_coefficients, real_cyclotomic_polynomial
    if type(samples) is not int or not 128 <= samples <= 10000:
        raise ValueError('sample budget in 128..10000 required')
    response = angular_response(potential)
    c = np.array(list(map(float, fourier_coefficients(potential))))
    norm = np.linalg.norm(c[1:]); rng = np.random.default_rng(seed)
    noise = rng.normal(size=(samples, len(c) - 1))
    studies = []
    for scale in (1e-4, 1e-3, 1e-2):
        angles = []
        for row in noise:
            cp = c.copy(); cp[1:] += scale * norm / np.sqrt(len(row)) * row
            angles.append(_fourier_global_minimum(cp))
        angles = np.array(angles); cs = 1 - 2 * np.cos(12 * angles)
        valid = (cs >= 0) & (cs <= 2)
        w = cs[valid] * vus * vcb
        for _ in range(5):
            w -= (w - w ** 3 - cs[valid] * vus * vcb) / (1 - 3 * w * w)
        studies.append({'relative_rms_fourier_noise': scale,
                        'phase_degrees68': list(map(float, np.quantile(np.degrees(angles), [.16, .84]))),
                        'coefficient68': list(map(float, np.quantile(cs, [.16, .84]))),
                        'Vub68_given_valid_chart': list(map(float, np.quantile(w, [.16, .84]))),
                        'invalid_chart_fraction': float(1 - valid.mean()),
                        'leaves_66_degree_basin_fraction': float(np.mean(abs(np.degrees(angles) - 66) > 10))})
    # Perturb all four selector coefficients; the common Psi60 factor is retained.
    psi = np.array(list(map(float, real_cyclotomic_polynomial(60))))
    q = np.array([-1., 3., 0., -1.])
    structured = []
    for scale in (.01, .05, .10):
        phases = []
        for row in noise[:512, :4]:
            d = np.polynomial.polynomial.polymul(psi, q + scale * np.linalg.norm(q) / 2 * row)
            v = np.r_[0, d / np.arange(1, len(d) + 1)]
            phases.append(numerical_minima(v)['angles'][0])
        structured.append({'relative_rms_multiplier_noise': scale, 'samples': len(phases),
                           'remains_at_66_fraction': float(np.mean(abs(np.array(phases) - 66) < 1e-6))})
    return {'seed': seed, 'samples': samples, 'generic_fourier': studies, 'structured_multiplier': structured,
            'linear_response': response,
            'scope': 'hypothetical independent CP-even coupling perturbations; no asserted radiative uncertainty distribution'}
