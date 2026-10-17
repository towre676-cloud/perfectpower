"""Independent exact geometry, Bernoulli and integral-factor checks."""
from fractions import Fraction
import unittest

from perfectpower import coxeter_mellin as cm
from perfectpower import e8_periods as e8


class TestCoxeterMellin(unittest.TestCase):
    def test_all_classical_cartan_root_orbits_through_rank_sixteen(self):
        for family, first in (("A", 1), ("B", 2), ("C", 2), ("D", 4)):
            for rank in range(first, 17):
                with self.subTest(family=family, rank=rank):
                    r = cm.geometry_receipt(family, rank)
                    self.assertEqual(r["root_orbit_lengths"], [r["coxeter_number"]] * rank)
                    self.assertEqual(r["roots"], rank * r["coxeter_number"])

    def test_all_exceptional_geometry_and_repeated_D_exponent(self):
        for family, rank in (("E", 6), ("E", 7), ("E", 8), ("F", 4), ("G", 2)):
            with self.subTest(family=family, rank=rank):
                cm.geometry_receipt(family, rank)
        self.assertEqual(cm.exponents("D", 4), (1, 3, 3, 5))
        self.assertEqual(cm.roots("E", 8), tuple(sorted(e8.simple_root_coordinates(r) for r in e8.roots())))
        self.assertEqual(cm.coxeter_matrix("E", 8), e8.coxeter_matrix())

    def test_rational_factors_equal_independent_bernoulli_phase_sums(self):
        types = [(f, n) for f in ("A", "B", "C", "D") for n in range(4, 9)]
        types += [("A", 1), ("B", 2), ("E", 6), ("E", 7), ("E", 8), ("F", 4), ("G", 2)]
        for family, rank in types:
            for s in (2, 4, 6, 8, 10):
                with self.subTest(family=family, rank=rank, weight=s):
                    self.assertEqual(cm.even_pi_coefficient(family, rank, s),
                                     cm.bernoulli_pi_coefficient(family, rank, s))

    def test_unique_zero_classification_has_correct_exact_integer_signs(self):
        for family, ranks in (("A", range(1, 65)), ("D", range(4, 65)), ("E", (6, 7, 8))):
            for rank in ranks:
                self.assertEqual(cm.zeta_factor(family, rank, 2), 0)
                self.assertTrue(all(cm.zeta_factor(family, rank, s) < 0 for s in range(3, 12)))
        for family, rank in (("F", 4), ("G", 2)):
            self.assertEqual(cm.real_zero_classification(family, rank)["zero_count"], 0)
            self.assertTrue(all(cm.zeta_factor(family, rank, s) > 0 for s in range(2, 33)))

    def test_tune_any_integer_weight_without_allocating_high_rank_geometry(self):
        for weight in range(2, 129):
            r = cm.bc_zero_tuner(weight)
            n = r["rank"]
            self.assertEqual(n + 1, 2 ** (weight - 1))
            if n >= 2:
                for family in ("B", "C"):
                    self.assertEqual(cm.zeta_factor(family, n, weight), 0)
                    self.assertLess(cm.zeta_factor(family, n, weight + 1), 0)
                    if weight > 2:
                        self.assertGreater(cm.zeta_factor(family, n, weight - 1), 0)
            self.assertEqual(r["dimension"], n * (2 * n + 1))
        self.assertEqual(cm.bc_zero_tuner(4097)["rank"].bit_length(), 4096)
        with self.assertRaises(ValueError):
            cm.bc_zero_tuner(4098)

    def test_tuned_logarithmic_integral_and_E8_match_existing_engine(self):
        self.assertEqual(cm.tuned_log_pi_coefficient(2), Fraction(-1, 6))
        self.assertEqual(cm.tuned_log_pi_coefficient(4), Fraction(-1, 5145))
        for s in range(2, 18):
            self.assertEqual(cm.zeta_factor("E", 8, s), e8.combined_zeta_factor(s))
        for x in (Fraction(1, 7), Fraction(1, 2), Fraction(3, 4)):
            self.assertEqual(cm.kernel("E", 8, x), e8.combined_kernel(x))

    def test_BC_kernel_equals_characteristic_polynomial_derivative(self):
        for rank in range(2, 17):
            for x in (Fraction(1, 5), Fraction(1, 2), Fraction(4, 5)):
                h = 2 * rank
                reflection_kernel = -rank * x ** (rank - 1) / (1 + x ** rank)
                independent = rank * h * x ** (h - 1) / (1 - x ** h) + reflection_kernel
                self.assertEqual(cm.bc_kernel(rank, x), independent)

    def test_independent_Euclidean_BC_roots_have_full_signed_cycles(self):
        for family in ("B", "C"):
            for rank in range(2, 17):
                orbits = cm.bc_signed_cycle_orbits(family, rank)
                self.assertEqual(len(orbits), rank)
                self.assertTrue(all(len(o) == 2 * rank for o in orbits))
                roots = {r for o in orbits for r in o}
                self.assertEqual(len(roots), 2 * rank * rank)
                short_norm, long_norm = ((1, 2) if family == "B" else (2, 4))
                self.assertEqual({sum(x*x for x in r) for r in roots}, {short_norm, long_norm})

    def test_input_guards_and_symbolic_zero_values(self):
        for family, rank in (("B", 1), ("D", 3), ("E", 5), ("F", 5), ("G", 3), ("H", 3)):
            with self.assertRaises(ValueError):
                cm.zeta_factor(family, rank, 2)
        for s in (True, 1, 2.0):
            with self.assertRaises(ValueError):
                cm.zeta_factor("A", 4, s)
        with self.assertRaises(ValueError):
            cm.zeta_factor("B", 10 ** 20, 100, bit_budget=64)
        self.assertEqual(cm.real_zero_classification("B", 7)["integer_zero"], 4)
        self.assertIsNone(cm.real_zero_classification("B", 6)["integer_zero"])


if __name__ == "__main__":
    unittest.main()
