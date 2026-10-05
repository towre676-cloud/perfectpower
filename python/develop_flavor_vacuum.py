"""Build the exact vacuum mechanism receipts; no experimental targets read.

PYTHONPATH=python OPENBLAS_NUM_THREADS=1 python python/develop_flavor_vacuum.py
"""
from pathlib import Path
from fractions import Fraction as Q
from math import gcd, pi
import hashlib
import json
import numpy as np
from perfectpower import polyalg as P
from perfectpower.core import evaluate, mul
from perfectpower.quotient_algebra import QuotientAlgebra
from perfectpower.cyclotomic_vacuum import (
    cyclotomic_polynomial, real_cyclotomic_polynomial, cosine_polynomials,
    phase_potential, fourier_coefficients, stationary_coupling_constraints,
    certify_global_minimum, golden_portal_identity)
from perfectpower.flavor_vacuum import (
    weyl_order_census, minimum_signed_dimension, integer_transfer_census, selector_census,
    vacuum_predictions, perturbation_study, vacuum_occupation, portal_diagnostic)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts/flavor_vacuum'


def save(name, data):
    (OUT / name).write_text(json.dumps(data, sort_keys=True, indent=2) + '\n')


def main():
    OUT.mkdir(exist_ok=True)
    anchors = json.loads((ROOT / 'receipts/flavor_prediction/training.json').read_text())
    # Only the two anchor magnitudes enter CKM consequences. No gamma, Rtdts,
    # Vub or sin2beta contributes to the mechanism construction calculation.
    u, v = anchors['Vus']['mean'], anchors['Vcb']['mean']
    save('weyl_obstruction.json', weyl_order_census())
    save('minimum_signed_dimension.json', minimum_signed_dimension())
    save('integer_transfer.json', integer_transfer_census())
    psi = real_cyclotomic_polynomial(60)
    algebra = QuotientAlgebra(cyclotomic_polynomial(60))
    z = algebra.element([0, 1]); x = z + z ** -1
    # Independent carrier substitution of the real polynomial.
    result = algebra.element(0)
    for a in reversed(psi):
        result = result * x + algebra.element(a)
    if result.coefficients != P.ZERO:
        raise AssertionError('real cyclotomic reduction failed')
    save('real_carrier.json', {**golden_portal_identity(), 'primitive_phase_degree': algebra.degree,
                             'real_phase_degree': P.degree(psi),
                             'real_identity_remainder': list(map(str, result.coefficients)),
                             'minimum_nonconstant_rational_harmonic_for_stationarity': P.degree(psi) + 1})
    constraints = stationary_coupling_constraints(60, 12)
    save('coupling_constraints.json', constraints)
    save('sparse_coupling_constraints.json', stationary_coupling_constraints(60, 12, (2, 3, 5, 8, 9, 12)))
    potentials = [('bare_antiderivative', (1,)), ('symmetric_selector', (0, 2, 0, -1)),
                  ('selected_cp_potential', (-1, 3, 0, -1))]
    for name, q in potentials:
        potential = phase_potential(60, q)
        certificate = certify_global_minimum(potential)
        for point in certificate['critical_points']:
            a, b = map(Q, point['x_interval'])
            point['phase_degrees_numerical_label'] = float(np.degrees(np.arccos(np.clip(float((a + b) / 2) / 2, -1, 1))))
        fc = fourier_coefficients(potential)
        derivative_remainder = P.divmod_poly(P.derivative(potential), psi)[1]
        payload = {'name': name, 'multiplier': list(q), 'potential_coefficients': list(map(str, potential)),
                   'cosine_coefficients': list(map(str, fc)), 'harmonics': len(fc) - 1,
                   'phase_derivative_remainder': list(map(str, derivative_remainder)),
                   'minimum_certificate': certificate, 'CKM_consequences': vacuum_predictions(potential, u, v),
                   'nonzero_harmonic_gcd': gcd(*(i for i, a in enumerate(fc) if i and a)),
                   'scope': 'constructed dimensionless angular EFT; potential selected retrospectively; no UV protection derived'}
        if name == 'selected_cp_potential':
            winner = certificate['winner_index']
            if winner is None:
                raise AssertionError('no exact global winner')
            a, b = map(Q, certificate['critical_points'][winner]['x_interval'])
            if not Q(4, 5) < a < b < Q(9, 10):
                raise AssertionError('global winner is not the positive 66-degree conjugate')
            payload['joint_portal'] = 'U(theta,C)=V(2cos(theta))+kappa*(C-1+2cos(12theta))^2, kappa>0'
            from perfectpower.flavor_prediction import ckm_from_depth
            payload['observable_portal_diagnostic'] = portal_diagnostic(ckm_from_depth((3-np.sqrt(5))/2, 11*pi/30, u, v))
            save('perturbations.json', perturbation_study(potential, u, v))
            save('occupation.json', vacuum_occupation(potential))
        save(name + '.json', payload)
    census = selector_census()
    save('selector_census.json', census)
    six = [r for r in census['records'] if len(r['angles']) == 1 and abs(r['angles'][0] - 66) < 1e-5]
    save('summary.json', {'structural_input': 'order60 carrier from previous candidate; no new physical mechanism selection data',
                         'anchors': {'Vus': u, 'Vcb': v}, 'order60_in_B5': False,
                         'selected_multiplier': [-1, 3, 0, -1], 'global_minima_full_circle': ['11*pi/30', '-11*pi/30'],
                         'coefficient': '(3-sqrt(5))/2', 'CP_sign_selected': False,
                         'stationarity_rational_constraints': constraints['rational_constraints'],
                         'census_count': census['primitive_multiplier_count'], 'census_single_66_count': len(six),
                         'minimum_l1_single_66': min(r['l1'] for r in six),
                         'UV_symmetry_protection': 'not established', 'new_lean_theorems': 0,
                         'status': 'explicit stable conditional vacuum mechanism; not an independently derived explanation of nature'})
    manifest = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.glob('*.json'))
                if p.name not in ('manifest.json', 'validation.json', 'sources.json')}
    save('manifest.json', manifest)
    print('exact global minimum: +/-66 degrees; golden portal; declared selector census:', len(census['records']))


if __name__ == '__main__':
    main()
