import unittest
from fractions import Fraction as Q
from math import pi
from perfectpower import polyalg as P
from perfectpower.core import evaluate, mul
from perfectpower.cyclotomic_vacuum import (
    cyclotomic_polynomial, real_cyclotomic_polynomial, cosine_polynomials,
    phase_potential, fourier_coefficients, stationary_coupling_constraints,
    isolate_real_roots, interval_evaluate, certify_global_minimum, golden_portal_identity)
from perfectpower.flavor_vacuum import signed_permutation_order, weyl_order_census, minimum_signed_dimension, integer_transfer_census


class ExactVacuum(unittest.TestCase):
    def test_cyclotomic_independent_laurent_substitution(self):
        # Build z^m Psi(z+1/z) by binomial Laurent expansion, independently
        # of the recurrence used to construct Psi.
        from math import comb
        for n in (5, 7, 12, 30, 60):
            psi = real_cyclotomic_polynomial(n); m = len(psi) - 1
            expanded = [Q(0)] * (2 * m + 1)
            for k, c in enumerate(psi):
                for j in range(k + 1):
                    expanded[m + k - 2 * j] += c * comb(k, j)
            self.assertEqual(P.poly(expanded), cyclotomic_polynomial(n))
        self.assertEqual(list(map(int, real_cyclotomic_polynomial(60))), [1, 0, -8, 0, 14, 0, -7, 0, 1])

    def test_exact_global_selection_not_just_stationarity(self):
        v = phase_potential(60, (-1, 3, 0, -1))
        result = certify_global_minimum(v, bits=48)
        self.assertEqual(result['status'], 'unique_global_minimum_in_x')
        a, b = map(Q, result['critical_points'][result['winner_index']]['x_interval'])
        self.assertTrue(Q('0.8') < a < b < Q('0.9'))
        self.assertGreater(Q(result['energy_gap_lower_bound']), Q('0.060'))
        self.assertEqual(len(result['critical_points']), 13)
        # A stationary 66-degree root exists in the simplest antiderivative,
        # but that potential's global winner is a different conjugate.
        bare = certify_global_minimum(phase_potential(60), bits=48)
        ba, bb = map(Q, bare['critical_points'][bare['winner_index']]['x_interval'])
        self.assertTrue(Q('-1.5') < ba < bb < Q('-1.4'))

    def test_symmetric_ties_are_retained(self):
        r = certify_global_minimum(phase_potential(60, (0, 2, 0, -1)), bits=40)
        self.assertIsNone(r['winner_index']); self.assertEqual(len(r['eligible_indices']), 2)

    def test_fourier_sparse_force_identity(self):
        v = phase_potential(60, (-1, 3, 0, -1)); f = fourier_coefficients(v)
        expected = [Q('11/12'), 0, 1, Q('2/3'), 0, Q('2/5'), 0, 0, Q('1/4'), Q('-2/9'), 0, 0, Q('-1/6')]
        self.assertEqual(list(f), expected)
        reconstructed = P.poly([f[0]])
        ss = cosine_polynomials(12)
        for n in range(1, 13):
            reconstructed = P.add(reconstructed, P.scale(ss[n], f[n] / 2))
        self.assertEqual(v, reconstructed)
        self.assertEqual(stationary_coupling_constraints(60, 8)['stationary_family_dimension'], 0)
        c = stationary_coupling_constraints(60, 12)
        self.assertEqual((c['rational_constraints'], c['stationary_family_dimension']), (8, 4))
        c = stationary_coupling_constraints(60, 12, (2, 3, 5, 8, 9, 12))
        self.assertEqual((c['rational_constraints'], c['stationary_family_dimension']), (4, 2))
        # The particular six coefficients lie in the exact constraint kernel.
        active = [f[n] for n in c['active_harmonics']]
        self.assertTrue(all(sum(Q(a) * b for a, b in zip(row, active)) == 0 for row in c['matrix']))

    def test_root_isolation_endpoints_and_repeated_roots(self):
        # (x+2)(x-1)^2(x-2); -2 excluded, 1 and 2 retained.
        roots = isolate_real_roots(mul(mul((2, 1), (1, -2, 1)), (-2, 1)), bits=20)
        self.assertEqual(len(roots), 2)
        self.assertTrue(any(a < 1 <= b for a, b in roots))
        self.assertTrue(any(a < 2 <= b for a, b in roots))
        endpoint = certify_global_minimum((4, -4, 1), bits=20)
        self.assertEqual(endpoint['status'], 'unique_global_minimum_in_x')
        self.assertEqual(endpoint['critical_points'][endpoint['winner_index']]['x_interval'], ['2', '2'])
        lo, hi = interval_evaluate((1, 2, -3), (Q(-1), Q(2)))
        for x in (Q(-1), Q('1/3'), Q(2)):
            self.assertTrue(lo <= evaluate((1, 2, -3), x) <= hi)

    def test_golden_portal_and_integer_extremality(self):
        self.assertEqual(golden_portal_identity()['golden_identity_remainder'], ['0'])
        r = integer_transfer_census(20)
        self.assertEqual(r['minimal_nontrivial_trace'], 3)
        self.assertEqual(len(r['extremizers']), 4)
        self.assertTrue(all(a['characteristic_polynomial'] == [1, -3, 1] for a in r['extremizers']))

    def test_exact_observable_eliminant_independently(self):
        from perfectpower.flavor_vacuum import cyclotomic_portal_polynomial
        u, v, w, d = Q('1/16'), Q('1/25'), Q('1/100'), Q('1/20000')
        s = 1-w; a = (u*v+w*(s-u)*(s-v)-d*s*s)**2; b = 4*u*v*(s-u)*(s-v)*w
        # Independent double-angle Chebyshev recurrence: cos(12theta)
        # = T6(cos(2theta)), cos(2theta)=2*cos(theta)^2-1.
        y = 2*a/b-1; t0, t1 = Q(1), y
        for _ in range(2, 7):
            t0, t1 = t1, 2*y*t1-t0
        residual = cyclotomic_portal_polynomial(u, v, w, d)
        self.assertEqual(residual/(u*v*b**12), (1-2*t1)**2-w*s*s/(u*v))
        with self.assertRaises(ValueError): cyclotomic_portal_polynomial(.1, v, w, d)

    def test_group_census_and_independent_matrix_orders(self):
        r = weyl_order_census(); self.assertEqual(r['group_order'], 3840)
        self.assertFalse(r['contains_order60']); self.assertEqual(set(map(int, r['element_order_counts'])), {1, 2, 3, 4, 5, 6, 8, 10, 12})
        # Exhaustively power every dimension-three signed matrix independently.
        from itertools import permutations, product
        for p in permutations(range(3)):
            for s in product((-1, 1), repeat=3):
                state = tuple((i, 1) for i in range(3)); count = 0
                while True:
                    state = tuple((p[i], parity * s[i]) for i, parity in state); count += 1
                    if state == tuple((i, 1) for i in range(3)):
                        break
                self.assertEqual(count, signed_permutation_order(p, s))
        self.assertEqual(minimum_signed_dimension()['minimum_dimension'], 10)

    def test_guards(self):
        for order in (True, 0, 121):
            with self.assertRaises(ValueError): real_cyclotomic_polynomial(order)
        with self.assertRaises(ValueError): phase_potential(60, (.2, 1))
        with self.assertRaises(ValueError): isolate_real_roots((0,))
        with self.assertRaises(ValueError): stationary_coupling_constraints(60, 12, (2, 2))


class NumericalPhysics(unittest.TestCase):
    def test_occupation_and_joint_stability(self):
        import numpy as np
        from perfectpower.flavor_vacuum import vacuum_occupation, angular_response
        v = phase_potential(60, (-1, 3, 0, -1))
        r = vacuum_occupation(v, grid=16384)
        basins = r['gradient_basins_positive_half_circle']
        self.assertAlmostEqual(sum(b['uniform_initial_fraction'] for b in basins), 1.)
        b66 = next(i for i, b in enumerate(basins) if abs(b['minimum_degrees'] - 66) < 1e-6)
        self.assertAlmostEqual(basins[b66]['uniform_initial_fraction'], .2, places=12)
        self.assertGreater(r['Gibbs_positive_half_circle'][-1]['basin_probabilities'][b66], .99)
        for row in r['Gibbs_positive_half_circle']:
            self.assertAlmostEqual(sum(row['basin_probabilities']), 1.)
        response = angular_response(v); h = response['angular_curvature']; fp = response['coefficient_derivative_per_radian']
        for kappa in (.01, 1., 100.):
            matrix = [[h + 2*kappa*fp*fp, -2*kappa*fp], [-2*kappa*fp, 2*kappa]]
            self.assertTrue(np.all(np.linalg.eigvalsh(matrix) > 0))
            self.assertAlmostEqual(np.linalg.det(matrix) / (2*kappa*h), 1., places=10)

    def test_response_against_independent_minimization(self):
        import numpy as np
        from scipy.optimize import minimize_scalar
        from perfectpower.flavor_vacuum import angular_response, _fourier_global_minimum
        v = phase_potential(60, (-1, 3, 0, -1)); r = angular_response(v)
        self.assertGreater(r['angular_curvature'], 12)
        f = np.array(list(map(float, fourier_coefficients(v)))); n = np.arange(len(f))
        for j in (1, 5, 12):
            cp = f.copy(); cp[j] += 1e-5
            # Bounded scalar minimization around the known isolated minimum
            # is independent of the Laurent-root route.
            solution = minimize_scalar(lambda t: np.sum(cp * np.cos(n * t)), bounds=(1., 1.3), method='bounded', options={'xatol': 1e-14})
            root = _fourier_global_minimum(cp)
            self.assertAlmostEqual(root, solution.x, places=7)
            cm = f.copy(); cm[j] -= 1e-5
            derivative = (root - _fourier_global_minimum(cm)) / 2e-5
            self.assertAlmostEqual(derivative, r['dtheta_depsilon_radians'][j - 1], places=5)

    def test_yukawa_embedding_rephasing_and_jarlskog(self):
        import numpy as np
        from perfectpower.flavor_prediction import ckm_from_depth, observables
        from perfectpower.flavor_vacuum import yukawa_embedding, portal_diagnostic
        V = ckm_from_depth((3 - np.sqrt(5)) / 2, 11 * pi / 30, .22431, .0411)
        Yu, Yd = yukawa_embedding(V, [1, 2, 5], [1, 3, 6])
        Hu, Hd = Yu @ Yu.conj().T, Yd @ Yd.conj().T
        commutator = Hu @ Hd - Hd @ Hu
        du = np.prod([b*b - a*a for a, b in ((1, 2), (1, 5), (2, 5))])
        dd = np.prod([b*b - a*a for a, b in ((1, 3), (1, 6), (3, 6))])
        self.assertAlmostEqual(np.linalg.det(commutator).imag / (2 * du * dd), observables(V)['J'], places=15)
        self.assertLess(abs(np.angle(np.linalg.det(Yu) * np.linalg.det(Yd))), 1e-15)
        rephased = np.diag(np.exp(1j * np.array([.1, .7, -.2]))) @ V @ np.diag(np.exp(1j * np.array([.2, -.6, .4])))
        for key, value in observables(V).items():
            self.assertAlmostEqual(float(value), float(observables(rephased)[key]), places=13)
        self.assertLess(abs(portal_diagnostic(V)['normalized_portal_residual']), 1e-13)
        self.assertAlmostEqual(portal_diagnostic(V)['normalized_portal_residual'], portal_diagnostic(rephased)['normalized_portal_residual'], places=12)


if __name__ == '__main__':
    unittest.main()
