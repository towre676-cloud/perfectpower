"""Independent geometric, matrix, divisor, and Bernoulli checks for E8."""
from fractions import Fraction

import unittest

from perfectpower import e8_periods as e8


class TestE8Periods(unittest.TestCase):
    def test_root_coordinates_and_all_1920_simple_reflections(self):
        roots = set(e8.roots())
        assert len(roots) == 240
        assert sum(all(x % 2 == 0 for x in r) for r in roots) == 112
        assert sum(all(x % 2 for x in r) for r in roots) == 128
        for root in roots:
            assert sum(x*x for x in root) == 8
            assert tuple(-x for x in root) in roots
            for simple in e8.SIMPLE_ROOTS:
                reflected = e8.reflect(root, simple)
                assert reflected in roots
                assert e8.reflect(reflected, simple) == root


    def test_cartan_graph_and_coxeter_polynomial_order(self):
        a = e8.cartan_matrix()
        edges = {(i, j) for i in range(8) for j in range(i + 1, 8) if a[i][j] == -1}
        assert edges == {(0, 2), (1, 3), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7)}
        c = e8.coxeter_matrix()
        assert e8.characteristic_polynomial(c) == e8.PHI30
        assert e8.matrix_power(c, 30) == e8.identity()
        for power in range(1, 30):
            assert e8.matrix_power(c, power) != e8.identity()
        assert e8.matmul(e8.matmul(tuple(zip(*c)), a), c) == a


    def test_matrix_and_coordinate_actions_agree_on_a_basis(self):
        c = e8.coxeter_matrix()
        for j, root in enumerate(e8.SIMPLE_ROOTS):
            image = tuple(sum(c[i][j] * e8.SIMPLE_ROOTS[i][k] for i in range(8)) for k in range(8))
            assert image == e8.coxeter_action(root)


    def test_displayed_roots_are_an_actual_simple_base(self):
        coefficients = [e8.simple_root_coordinates(r) for r in e8.roots()]
        assert sum(all(c >= 0 for c in v) for v in coefficients) == 120
        assert sum(all(c <= 0 for c in v) for v in coefficients) == 120
        for root, v in zip(e8.roots(), coefficients):
            assert tuple(sum(v[i] * e8.SIMPLE_ROOTS[i][j] for i in range(8)) for j in range(8)) == root
        assert max(sum(v) for v in coefficients) == 29  # highest-root height h-1


    def test_384_dimensions_restrict_to_48_actual_coxeter_modules(self):
        assert e8.restricted_cyclotomic_multiplicities() == dict.fromkeys(e8.EXPONENTS, 48)
        assert sum(e8.restricted_cyclotomic_multiplicities().values()) == 384


    def test_actual_root_orbits_and_nontrivial_fixed_points(self):
        orbits = e8.root_orbits()
        assert len(orbits) == 8
        assert all(len(orbit) == 30 for orbit in orbits)
        assert {r for orbit in orbits for r in orbit} == set(e8.roots())
        # Count actual permutation fixed points rather than infer from dimensions.
        for power in (1, 2, 3, 5, 6, 10, 15, 30):
            fixed = 0
            for root in e8.roots():
                image = root
                for _ in range(power):
                    image = e8.coxeter_action(image)
                fixed += image == root
            assert fixed == (240 if power == 30 else 0)


    def test_traces_match_independent_ramanujan_divisor_sum(self):
        for power in range(-30, 61):
            assert e8.coxeter_trace(power) == e8.ramanujan_sum_30(power)
        assert e8.coxeter_trace(1) == -1
        assert e8.coxeter_trace(15) == -8


    def test_two_independent_exact_integral_evaluations(self):
        for s in range(2, 18, 2):
            assert e8.spectral_pi_coefficient(s) == e8.bernoulli_spectral_pi_coefficient(s)
        assert e8.spectral_pi_coefficient(2) == Fraction(-2, 45)
        assert e8.spectral_zeta_factor(2) == Fraction(-4, 15)
        assert e8.root_permutation_zeta_factor(2) == Fraction(4, 15)


    def test_248_dimensional_model_cancellation_and_derivative(self):
        assert e8.combined_zeta_factor(2) == 0
        assert e8.combined_pi_coefficient(2) == 0
        assert all(e8.combined_zeta_factor(s) < 0 for s in range(3, 15))
        assert e8.combined_log_mellin_coefficients() == {
            2: Fraction(-4, 45), 3: Fraction(-1, 15), 5: Fraction(-1, 18)}
        # A separate Bernoulli sum over actual cyclic root orbits and Cartan
        # eigenphases establishes cancellation without the zeta-factor formula.
        phases = [Fraction(j, 30) for orbit in e8.root_orbits() for j in range(len(orbit))]
        phases.extend(Fraction(m, 30) for m in e8.EXPONENTS)
        assert len(phases) == 248
        assert sum(e8.bernoulli_polynomial(2, x) for x in phases) == 0


    def test_rational_kernel_matches_divisor_filter(self):
        mu = {1: 1, 2: -1, 3: -1, 5: -1, 6: 1, 10: 1, 15: 1, 30: -1}
        for x in (Fraction(1, 7), Fraction(1, 2), Fraction(3, 4), Fraction(-1, 3)):
            filtered = sum(Fraction(mu[30 // d] * d) * x ** (d - 1) / (1 - x ** d) for d in mu)
            assert e8.spectral_kernel(x) == filtered


    def test_invalid_integral_orders(self):
        for value in (0, 1, -2, 2.5, True):
            with unittest.TestCase().assertRaises(ValueError):
                e8.spectral_zeta_factor(value)


    def test_receipt_replays_exact_construction(self):
        result = e8.receipt()
        assert result["root_orbit_lengths"] == [30] * 8
        assert result["pi_coefficients"]["2"] == "-2/45"
        assert result["cyclotomic_bridge"]["power_to_coxeter_phase"] == 56
        assert result["combined_model"]["pi_coefficients"]["2"] == "0"
