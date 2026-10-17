"""Independent structural and enclosure checks for the recovered deep engine."""
import json
import unittest
from fractions import Fraction as Q
from math import factorial
from perfectpower.raghava_generating import (
    lambda_coefficients, generating_multiplier, generating_family, verify_family,
    canonical_second_basis, two_order_decomposition, zeta_interval,
    family_partial, family_interval, generator_interval, resolvent_interval,
    normalization_interval, master_interval, global_taylor_bounds,
    global_generator_interval,
)
from perfectpower.raghava_periods import two_order_cancellation


def bounds(receipt):
    return Q(receipt['lower']), Q(receipt['upper'])


def overlap(a, b):
    return max(a[0], b[0]) <= min(a[1], b[1])


class GeneratingCoefficientsTests(unittest.TestCase):
    def test_reciprocal_series_all_65_coefficients(self):
        values = lambda_coefficients(64)
        self.assertEqual(values[:4], (Q(1), -Q(1, 6), Q(7, 360), -Q(31, 15120)))
        for m in range(1, 65):
            self.assertEqual(sum((values[m-k]/factorial(2*k+1) for k in range(m+1)), Q(0)), 0)
            self.assertGreater((-1)**m*values[m], 0)

    def test_small_published_families(self):
        expected = {
            (0, 'second'): ['5/3'], (1, 'second'): ['19/54', '-77/18'],
            (2, 'second'): ['-187/17496', '-4249/2916', '62665/3888'],
            (0, 'supplementary'): ['1/2'], (1, 'supplementary'): ['1/162', '-7/108'],
            (2, 'supplementary'): ['13/1399680', '-7/5184', '689/62208'],
        }
        for (m, kind), coefficients in expected.items():
            self.assertEqual([row['coefficient'] for row in generating_family(m, kind)['zeta_coefficients']], coefficients)

    def test_second_diagonal_nonzero_and_exact(self):
        for m in range(65):
            diagonal = Q(72*144**m+40*16**m+9*9**m-1, 72*36**m)
            self.assertEqual(generating_multiplier(0, m), diagonal)
            self.assertGreater(diagonal, 0)

    def test_supplementary_multiplier_by_formal_cosine_convolution(self):
        values = lambda_coefficients(12)
        for k in range(13):
            for j in [0, 1, 3, 8]:
                mu = (-1)**k*values[k]
                cosine = sum(((-1)**(k-h)*values[k-h]*Q((-1)**h, factorial(2*h))
                              for h in range(k+1)), Q(0))
                half = sum(((-1)**(k-h)*values[k-h]*Q((-1)**h, 4**h*factorial(2*h))
                            for h in range(k+1)), Q(0))
                actual = ((cosine+mu)/(9*9**j)+(2*cosine+3*mu-4*half)/(8*4**j)
                          +(4*half-mu)/(72*36**j)+half/(8*16**j)-half/(72*144**j))
                self.assertEqual(actual, mu*generating_multiplier(k, j, 'supplementary'))

    def test_every_legacy_selected_order_recovered(self):
        for s in range(2, 17):
            for r in range(1, s):
                actual, legacy = two_order_decomposition(r, s), two_order_cancellation(r, s)
                for key in ['A', 'D', 'harmonic_coefficients', 'zeta_coefficients']:
                    self.assertEqual(actual[key], legacy[key], (r, s, key))

    def test_formal_basis_supplementary_through_32(self):
        for m in range(33):
            actual = canonical_second_basis(m, generating_family(m, 'supplementary'))
            self.assertTrue(actual['reconstruction_checked'])
            self.assertEqual(actual['input_coefficients'], actual['reconstructed_coefficients'])

    def test_arbitrary_formal_vector_and_basis_unit(self):
        m = 12
        values = [Q((-1)**k, k+1) for k in range(m+1)]
        result = canonical_second_basis(m, values)
        self.assertEqual(list(map(Q, result['reconstructed_coefficients'])), values)
        result = canonical_second_basis(m, generating_family(m))
        self.assertEqual(list(map(Q, result['second_coefficients'])), [Q(0)]*m+[Q(1)])

    def test_receipt_roundtrip_and_tamper(self):
        r = json.loads(json.dumps(generating_family(64)))
        self.assertTrue(verify_family(r))
        r['zeta_coefficients'][0]['coefficient'] = '0'
        self.assertFalse(verify_family(r))


class GeneratingEnclosuresTests(unittest.TestCase):
    def test_zeta_even_known_pi_values(self):
        from perfectpower.cyclotomic_real import pi_interval
        p = pi_interval(100)
        for s, c in [(2, Q(1, 6)), (4, Q(1, 90)), (6, Q(1, 945))]:
            value = zeta_interval(s, 80)
            self.assertTrue(overlap(value, (p[0]**s*c, p[1]**s*c)))
            self.assertLess(value[1]-value[0], Q(1, 1 << 80))

    def test_original_sums_and_independent_zeta_enclosures(self):
        for m in range(13):
            for kind in ['second', 'supplementary']:
                original = family_partial(m, kind, terms=48, bits=96)
                reduced = family_interval(m, kind, bits=96)
                self.assertTrue(overlap(bounds(original), bounds(reduced)), (m, kind))
                if kind == 'second':
                    lo, hi = bounds(reduced)
                    self.assertGreater(lo if m%2 == 0 else -hi, 0)

    def test_direct_oscillatory_termination(self):
        for j, expected in [(1, Q(1, 2)), (2, Q(3, 4))]:
            value = generator_interval(1, j, terms=1, oscillatory=True)
            self.assertEqual(bounds(value), (expected, expected))
            self.assertTrue(value['terminated'])
        self.assertTrue(generator_interval(2, 1, 2, True)['terminated'])

    def test_master_both_conventions_and_nontrivial_parameters(self):
        for oscillatory in [False, True]:
            for x in ['0', '1/20', '1/4', '-1/3']:
                value = master_interval(x, terms=48, bits=80, oscillatory=oscillatory)
                self.assertTrue(value['intervals_overlap'], (x, oscillatory))
                self.assertLessEqual(Q(value['difference'][0]), 0)
                self.assertGreaterEqual(Q(value['difference'][1]), 0)

    def test_normalization_doubling(self):
        from perfectpower.raghava_generating import _entire_positive_series
        from perfectpower.cyclotomic_real import pi_interval
        p = pi_interval(120)
        for x in [Q(1, 4), Q(1), Q(4)]:
            a = bounds(normalization_interval(x, bits=80))
            b = bounds(normalization_interval(2*x, bits=80))
            c = (_entire_positive_series((p[0]*x/3)**2, 0, 96)[0],
                 _entire_positive_series((p[1]*x/3)**2, 0, 96)[1])
            self.assertTrue(overlap(a, (b[0]*c[0], b[1]*c[1])))

    def test_global_bounds_beyond_local_taylor_disk(self):
        for t in ['0', '1/4', '1', '4', '9']:
            local = bounds(global_taylor_bounds(t, order=3, bits=96))
            direct = bounds(global_generator_interval(t, terms=160, bits=96))
            self.assertTrue(overlap(local, direct), t)
            self.assertGreaterEqual(local[0], 0)
            self.assertGreater(direct[0], 0)

    def test_domain_guards(self):
        for callback in [lambda: generating_family(65), lambda: generating_family(-1),
                         lambda: generating_family(1, 'wrong'),
                         lambda: canonical_second_basis(33, []),
                         lambda: resolvent_interval(1), lambda: master_interval('1/2'),
                         lambda: generator_interval(17),
                         lambda: normalization_interval(3, oscillatory=True),
                         lambda: global_taylor_bounds(-1),
                         lambda: global_generator_interval(65)]:
            with self.assertRaises(ValueError):
                callback()


if __name__ == '__main__':
    unittest.main()
