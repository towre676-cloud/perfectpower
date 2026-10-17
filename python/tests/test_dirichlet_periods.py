"""Independent exact Fourier, finite-group, Euler, and analytic crosschecks."""

import cmath
from fractions import Fraction as Q
from math import gcd, log, pi, sqrt
import unittest

from perfectpower.dirichlet_periods import (
    CyclotomicNumber as C, DirichletCharacter, PeriodicDirichlet, all_characters,
)


class DirichletPeriodTests(unittest.TestCase):
    def test_exact_cyclotomic_arithmetic_and_embeddings(self):
        z = C.root(8)
        root_two = z + z.conjugate()
        self.assertEqual(root_two ** 2, 2)
        self.assertEqual(z ** 4, -1)
        self.assertEqual(z ** -1, z.conjugate())
        self.assertEqual(C.root(3).lift(12), C.root(12, 4))
        self.assertEqual(C.root(4) ** 2, C(1, -1))
        self.assertEqual((1 + z) / (1 + z), 1)
        self.assertEqual(C(20, Q(2, 7)).as_rational(), Q(2, 7))
        self.assertAlmostEqual(root_two.approximate().real, sqrt(2), places=14)
        with self.assertRaises(ValueError):
            z.as_rational()
        with self.assertRaises(ValueError):
            z.lift(6)
        with self.assertRaises(ZeroDivisionError):
            C(5, 0) ** -1

    def test_rational_mellin_kernels_and_endpoint_limits(self):
        beta = DirichletCharacter.beta().rational_period()
        eta = PeriodicDirichlet((1, -1))
        for x in (Q(0), Q(1, 5), Q(3, 7), Q(1)):
            self.assertEqual(beta.kernel(x), 1 / (1 + x * x))
            self.assertEqual(eta.kernel(x), 1 / (1 + x))
        self.assertEqual(beta.domain()['ordinary_series_and_mellin'], 'Re(s)>0')
        self.assertEqual(PeriodicDirichlet((1, 1)).domain()['pole_at_one_residue'], '1')
        self.assertEqual(PeriodicDirichlet((1, -1, 1, -1)).minimal_period, 2)
        self.assertEqual(beta.coefficient(0), 0)
        self.assertEqual(beta.coefficient(-1), -1)
        with self.assertRaises(ValueError):
            PeriodicDirichlet((1,)).kernel(1)
        with self.assertRaises(ValueError):
            beta.kernel(Q(7, 6))

    def test_hurwitz_lerch_indices_and_normalizations(self):
        p = PeriodicDirichlet((Q(2, 3), -1, 0, Q(7, 2)))
        h = p.hurwitz_reduction()
        self.assertEqual(h['factor'], '4^(-s)')
        self.assertEqual([(t['coefficient'], t['a']) for t in h['terms']],
                         [('2/3', '1/4'), ('-1', '1/2'), ('7/2', '1')])
        self.assertEqual([t['z_power'] for t in p.lerch_reduction()['terms']], [1, 2, 4])
        # Independent finite grouping verifies the scale N^-s and indexing a=1..N.
        for weight in (2, 3):
            blocks = sum((c / (4 * k + a) ** weight
                          for a, c in enumerate(p.coefficients, 1) for k in range(7)), Q(0))
            self.assertEqual(blocks, p.partial_sum(weight, 28))

    def test_exact_dft_roundtrip_for_every_small_period(self):
        for n in range(1, 13):
            p = PeriodicDirichlet(tuple(Q(((j * j + 3 * j) % 11) - 5, j + 1) for j in range(n)))
            self.assertEqual(p.inverse_dft(), p.coefficients, n)
            self.assertEqual(p.dft()[0], p.mean)
            for h, value in enumerate(p.dft()):
                expected = sum(float(c) * cmath.exp(-2j * pi * h * a / n)
                               for a, c in enumerate(p.coefficients, 1)) / n
                self.assertLess(abs(value.approximate() - expected), 2e-13)

    def test_beta_values_and_opposite_parity_scope(self):
        beta = DirichletCharacter.beta()
        for weight, coefficient in ((1, Q(1, 4)), (3, Q(1, 32)), (5, Q(5, 1536)), (7, Q(61, 184320))):
            self.assertEqual(beta.pi_coefficient(weight), coefficient)
            self.assertEqual(beta.gauss_pi_coefficient(weight), coefficient)
            self.assertTrue(beta.special_value(weight)['primitive_euler_crosscheck'])
        self.assertEqual(beta.special_value(2)['status'], 'formal')
        self.assertEqual(beta.rational_period().special_value(2)['status'], 'formal')
        with self.assertRaises(ValueError):
            beta.pi_coefficient(2)
        self.assertEqual(PeriodicDirichlet((1,)).pi_coefficient(2), Q(1, 6))
        self.assertEqual(PeriodicDirichlet((1,)).pi_coefficient(4), Q(1, 90))

    def test_nontrivial_algebraic_residue_pair(self):
        p = PeriodicDirichlet.residue_pair(8, 1)
        z = C.root(8)
        expected = (4 + 3 * (z + z.conjugate())) / 256
        self.assertEqual(p.pi_coefficient(3), expected)
        direct = sum(1 / (8 * n + 1) ** 3 - 1 / (8 * n + 7) ** 3 for n in range(2000))
        self.assertAlmostEqual(direct, float((4 + 3 * sqrt(2)) / 256) * pi ** 3, places=11)
        self.assertEqual(PeriodicDirichlet.residue_pair(2, 1).coefficients, (Q(0), Q(0)))

    def test_mean_zero_tail_enclosures_include_known_values(self):
        eta = PeriodicDirichlet((1, -1))
        beta = DirichletCharacter.beta().rational_period()
        for terms in (0, 1, 2, 7, 30, 101):
            for p, weight, actual in ((eta, 1, log(2)), (beta, 1, pi / 4), (beta, 3, pi ** 3 / 32)):
                lo, hi = p.enclosure(weight, terms)
                self.assertLessEqual(float(lo) - 1e-14, actual)
                self.assertGreaterEqual(float(hi) + 1e-14, actual)
        self.assertEqual(eta.tail_bound(1, 100), Q(1, 101))
        self.assertEqual(PeriodicDirichlet((0,)).tail_bound(1, 0), 0)
        with self.assertRaises(ValueError):
            PeriodicDirichlet((1,)).tail_bound(1, 100)

    def test_character_validation_and_full_complex_table(self):
        # Primitive quartic character mod 5: chi(2)=i.
        chi = DirichletCharacter(5, 4, (None, 0, 1, 3, 2))
        self.assertEqual(chi.value(2), C.root(4))
        self.assertEqual(chi.value(3), -C.root(4))
        self.assertEqual(chi.parity, -1)
        self.assertEqual(chi.conductor, 5)
        self.assertEqual(chi.conjugate().conjugate(), chi)
        self.assertEqual(DirichletCharacter(5, 8, (None, 0, 2, 6, 4)), chi)
        for a in range(5):
            for b in range(5):
                self.assertEqual(chi.value(a * b), chi.value(a) * chi.value(b))
        with self.assertRaises(ValueError):
            DirichletCharacter(5, 4, (None, 0, 1, 1, 2))
        with self.assertRaises(ValueError):
            DirichletCharacter(4, 2, (0, 0, None, 1))
        with self.assertRaises(ValueError):
            chi.rational_period()

    def test_conductors_induction_and_euler_factor(self):
        beta = DirichletCharacter.beta()
        induced = beta.induce(12)
        self.assertEqual(induced.conductor, 4)
        self.assertEqual(induced.primitive_character(), beta)
        self.assertFalse(induced.is_primitive)
        self.assertEqual(induced.euler_factors(3), ((3, C(2, Q(28, 27))),))
        self.assertEqual(induced.pi_coefficient(3), Q(7, 216))
        self.assertEqual(induced.pi_coefficient(3), induced.primitive_euler_pi_coefficient(3))
        self.assertEqual(DirichletCharacter.principal(12).conductor, 1)
        self.assertEqual(DirichletCharacter.principal(12).pi_coefficient(2), Q(1, 9))
        with self.assertRaises(ValueError):
            induced.gauss_pi_coefficient(3)
        with self.assertRaises(ValueError):
            beta.induce(6)

    def test_primitive_and_imprimitive_gauss_scope(self):
        for chi in all_characters(8):
            for a in range(chi.modulus):
                receipt = chi.gauss_relation(a)
                if receipt['applicable']:
                    self.assertTrue(receipt['exact_equality'], (chi.packet(), a))
        principal = DirichletCharacter.principal(4)
        self.assertEqual(principal.gauss_sum(1), 0)
        self.assertEqual(principal.gauss_sum(2), -2)
        self.assertFalse(principal.gauss_relation(2)['applicable'])
        self.assertIsNone(principal.gauss_relation(2)['exact_equality'])
        beta = DirichletCharacter.beta()
        self.assertEqual(beta.gauss_sum() * beta.gauss_sum().conjugate(), 4)

    def test_all_small_character_tables_and_independent_value_formula(self):
        count = 0
        for q in range(1, 17):
            chars = all_characters(q)
            units = [a for a in range(q) if gcd(a, q) == 1]
            self.assertEqual(len(chars), len(units), q)
            self.assertEqual(len(set((c.order, c.exponents) for c in chars)), len(chars))
            for chi in chars:
                self.assertEqual(sum((chi.value(a) for a in range(q)), C(chi.order, 0)),
                                 len(units) if chi.is_principal else 0)
                for weight in (1, 2, 3, 4):
                    if chi.parity == (-1) ** weight:
                        self.assertEqual(chi.pi_coefficient(weight), chi.primitive_euler_pi_coefficient(weight),
                                         (chi.packet(), weight))
                        count += 1
        self.assertGreater(count, 100)
        with self.assertRaises(ValueError):
            all_characters(129)

    def test_complex_character_kernel_and_tail_disk(self):
        chi = DirichletCharacter(5, 4, (None, 0, 1, 3, 2))
        self.assertEqual(chi.kernel(0), 1)
        self.assertEqual(chi.kernel(1), (3 + C.root(4)) / 5)
        for x in (Q(1, 7), Q(4, 5)):
            direct = sum((chi.value(a) * x ** (a - 1) for a in range(1, 6)), C(4, 0)) / (1 - x ** 5)
            self.assertEqual(chi.kernel(x), direct)
        exact = chi.pi_coefficient(3).approximate() * pi ** 3
        for terms in (0, 3, 14, 100):
            partial = chi.partial_sum(3, terms).approximate()
            self.assertLessEqual(abs(exact - partial), float(chi.tail_bound(3, terms)) + 1e-13)
        self.assertEqual(chi.domain()['ordinary_series_and_mellin'], 'Re(s)>0')

    def test_negative_integer_values_are_analytic_continuation(self):
        principal = DirichletCharacter.principal(1)
        self.assertEqual(principal.negative_integer_value(0), -Q(1, 2))
        self.assertEqual(principal.negative_integer_value(1), -Q(1, 12))
        self.assertEqual(principal.negative_integer_value(2), 0)
        self.assertEqual(DirichletCharacter.beta().negative_integer_value(0), Q(1, 2))
        self.assertEqual(DirichletCharacter.beta().negative_integer_value(1), 0)

    def test_invalid_exact_inputs(self):
        for values in ((), (0.1,), (True,)):
            with self.assertRaises(ValueError):
                PeriodicDirichlet(values)
        p = PeriodicDirichlet((1, -1))
        for weight in (0, True, 1.5):
            with self.assertRaises(ValueError):
                p.special_value(weight)
        with self.assertRaises(ValueError):
            p.partial_sum(2, -1)


if __name__ == '__main__':
    unittest.main()
