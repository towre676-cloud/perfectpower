"""Independent checks of the inputs shared by the flavor search.

Historical training data are left pinned. The PDG values below are a separately
identified 2026 comparison, not a refit or a joint likelihood.
"""
from itertools import product
from math import factorial, pi, sqrt
from pathlib import Path
import hashlib
import json
import sympy as s

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts/m22_interactions/flavor_input_audit.json'


def stationarity_certificate():
    # Independent Chebyshev construction, rather than the production recurrence.
    x = s.symbols('x')
    psi = s.minimal_polynomial(2 * s.cos(11 * s.pi / 30), x)
    basis = [s.Integer(1)] + [2 * s.chebyshevt(n, x / 2) for n in range(1, 13)]
    columns = [s.Poly(s.rem(s.diff(p, x), psi, x), x) for p in basis]
    matrix = s.Matrix(8, 13, lambda i, j: columns[j].nth(i))
    support = [2, 3, 5, 8, 9, 12]
    six = matrix[:, support]
    assert matrix.rank() == 8 and six.rank() == 4
    weights = s.Matrix([1, s.Rational(2, 3), s.Rational(2, 5),
                        s.Rational(1, 4), -s.Rational(2, 9), -s.Rational(1, 6)])
    assert six * weights == s.zeros(8, 1)
    # Over R, stationarity at one fixed interior angle is ONE real equation.
    angle = 11 * s.pi / 30
    real_coefficient = -2 * s.sin(2 * angle) / (3 * s.sin(3 * angle))
    assert s.simplify(-2 * s.sin(2 * angle) -
                      3 * real_coefficient * s.sin(3 * angle)) == 0
    return {'minimal_polynomial': str(psi), 'degree': 8,
            'rational_twelve_harmonic_rank': 8, 'rational_six_harmonic_rank': 4,
            'real_single_angle_rank': 1,
            'two_harmonic_real_stationary_example_c3': str(real_coefficient),
            'scope': 'Rational coefficients imply stationarity at all conjugate roots; real coefficients do not.'}


def sextic_gradient_certificate():
    """Compute the exact one-index reduced tensor, independently of link code."""
    field = s.QQ.algebraic_field(s.sqrt(5), s.I * s.sqrt(3))
    terms = json.loads((ROOT / 'receipts/m22_interactions/valentiner_invariants.json').read_text())['sextic']['terms']
    coefficients = {tuple(t['powers']): field.from_sympy(s.sympify(t['coefficient']))
                    for t in terms}
    tensor = {}
    for index in product(range(3), repeat=6):
        powers = tuple(index.count(j) for j in range(3))
        multiplicity = factorial(6) // __import__('math').prod(factorial(k) for k in powers)
        tensor[index] = coefficients.get(powers, field.zero) / field.convert(multiplicity)
    density = []
    for i in range(3):
        row = []
        for j in range(3):
            value = field.zero
            for tail in product(range(3), repeat=5):
                a, b = tensor[(i,) + tail], tensor[(j,) + tail]
                value += field.from_sympy(s.conjugate(field.to_sympy(a))) * b
            assert value == (field.convert(s.Rational(16, 3)) if i == j else field.zero)
            row.append(str(field.to_sympy(value)))
        density.append(row)
    # I6(L)=<T,T composed with L>. There are six equivalent index insertions.
    gradient = [[32 if i == j else 0 for j in range(3)] for i in range(3)]
    assert sum(gradient[i][i] for i in range(3)) == 6 * 16
    return {'exact_reduced_density': density, 'tensor_norm_squared': 16,
            'gradient_I6_at_identity': gradient, 'Euler_derivative_at_identity': 96,
            'canonical_F_potential_for_W_kappa_I6_on_rI': '3072*abs(kappa)^2*r^10',
            'nonzero_group_link_is_radially_stationary_for_sextic_only': False,
            'scope': 'An isolated holomorphic sextic does not generate the chosen nonzero scalar alignment vacuum. Other allowed superpotential, kinetic and soft terms must be matched.'}


def empirical_comparison():
    from perfectpower.flavor_prediction import ckm_from_depth, observables
    c = (3 - sqrt(5)) / 2
    u, v, w = .22431, .0407, .00389
    reference = observables(ckm_from_depth(c, 11 * pi / 30, .22431, .0411))
    updated = observables(ckm_from_depth(c, 11 * pi / 30, u, v))
    effective = w * (1 - w * w) / (u * v)
    # Linear error propagation; no covariance is available for this comparison.
    derivatives = [-(effective / u), -(effective / v), (1 - 3 * w * w) / (u * v)]
    sigma = sqrt(sum((a * b) ** 2 for a, b in zip(derivatives, [.00085, .0013, .00016])))
    return {'source': 'https://pdg.lbl.gov/2026/reviews/rpp2026-rev-ckm-matrix.pdf',
            'source_revision': 'March 2026', 'checked_date': '2026-10-06',
            'PDG_equations': {'Vus': '12.8', 'Vcb': '12.11', 'Vub': '12.12', 'sin2beta': '12.20'},
            'combined_measurements': {'Vus': [u, .00085], 'Vcb': [v, .0013],
                                      'Vub': [w, .00016], 'sin2beta': [.710, .011]},
            'reference_2025_anchor_predictions': {k: float(a) for k, a in reference.items()},
            'updated_anchor_conditional_predictions': {k: float(a) for k, a in updated.items()},
            'golden_coefficient': c, 'central_measured_effective_coefficient': effective,
            'independent_linear_sigma': sigma,
            'nominal_independent_error_offset_in_sigma': (effective - c) / sigma,
            'scope': 'Illustrative independent-error comparison, not a global fit, exclusion significance, posterior update or evidence of discovery. Historical inputs remain unchanged.'}


def main():
    record = {'schema': 'pp-flavor-input-audit/1', 'audited_commit': 'c7cdb4cf9814a7be006c17965678084b85211612',
              'stationarity': stationarity_certificate(),
              'sextic_scalar_matching': sextic_gradient_certificate(),
              'empirical': empirical_comparison()}
    paths = ['python/develop_valentiner_link.py', 'python/develop_valentiner_messenger.py',
             'python/develop_valentiner_cp.py', 'python/develop_m22_global_modes.py',
             'python/perfectpower/flavor_identifiability.py', 'receipts/flavor_prediction/training.json',
             'receipts/m22_interactions/valentiner_invariants.json',
             'receipts/m22_interactions/valentiner_cp.json', 'receipts/m22_interactions/valentiner_link.json',
             'receipts/m22_interactions/valentiner_messenger.json',
             'receipts/m22_interactions/m22_global_modes.json']
    record['input_sha256'] = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}
    OUT.write_text(json.dumps(record, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v for k, v in record.items() if k != 'input_sha256'}, indent=2))


if __name__ == '__main__':
    main()
