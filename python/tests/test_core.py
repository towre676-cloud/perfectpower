import unittest
import random
from fractions import Fraction
from math import gcd, isqrt
from perfectpower.core import (count, hit_indices, integer_power_root,
                               rigid_certificate, verify_certificate, windows,
                               power, normalize)

class TestExactDefinition(unittest.TestCase):
    def test_signed_and_boundary(self):
        self.assertEqual(integer_power_root(-27, 3), -3)
        self.assertIsNone(integer_power_root(-27, 2))
        self.assertEqual(integer_power_root(0, 7), 0)
        for d in (0, 1):
            with self.assertRaises(ValueError):
                integer_power_root(1, d)

    def test_parameters_affect_actual_hits(self):
        self.assertEqual(count((0, 1), 2, 0, 100), 10)
        self.assertEqual(count((0, 1), 3, 0, 100), 4)
        self.assertEqual(count((0, 1), 2, 1, 100), 9)
        self.assertEqual(count((0, 0, 1), 2, 0, 100), 100)

    def test_examples_and_mononomials(self):
        self.assertEqual([count((1, 0, 0, 1), 2, 0, N) for N in (1000, 10000)], [1, 1])
        self.assertEqual([count((1, 4), 2, 0, N) for N in (1000, 10000, 100000)], [31, 99, 315])
        for r, d, N in ((3, 2, 10000), (2, 3, 10000), (4, 6, 10000)):
            q = d // gcd(r, d)
            expected = sum(n ** q <= N for n in range(1, N + 1))
            self.assertEqual(count((0,) * r + (1,), d, 0, N), expected)
        self.assertEqual(count((0, 1, 1), 2, 0, 1000), 0)

    def test_surgery_exact_prefix(self):
        N0, N = 31, 1000
        base = {n for n, _ in hit_indices((0, 1), 2, 0, N)}
        changed = base | set(range(1, N0))
        D = len(changed & set(range(1, N0))) - len(base & set(range(1, N0)))
        for t in range(N0, N + 1):
            self.assertEqual(len(changed & set(range(1, t + 1))) - len(base & set(range(1, t + 1))), D)
        self.assertEqual(Fraction(D, N), Fraction(len(changed) - len(base), N))

    def test_windows_are_tail_local(self):
        w = windows((0, 1), 2, 0, 64)
        self.assertEqual(w[-1]['lo'], 64)
        self.assertEqual(w[-1]['max_ratio'], 1/8)

    def test_integer_root_against_independent_enumeration(self):
        for d in range(2, 8):
            for v in range(-100, 501):
                witness = [m for m in range(-25, 26) if m ** d == v]
                root = integer_power_root(v, d)
                self.assertEqual(root is not None, bool(witness), (d, v))
                if root is not None:
                    self.assertIn(root, witness)

class TestRigidCertificate(unittest.TestCase):
    def test_identity_and_finite_cutoff(self):
        for coeff, d, identity in [((0, 0, 1), 2, True), ((1, 2, 1), 2, True),
                                   ((0, 0, 0, 0, 1), 2, True),
                                   ((1, 0, 0, 0, 1), 2, False),
                                   ((0, 1, 1, 2, 1), 2, False),
                                   ((0,), 3, True)]:
            c = rigid_certificate(coeff, d)
            self.assertIsNotNone(c)
            self.assertTrue(verify_certificate(c), c)
            self.assertEqual(c.exact_identity, identity)
            if not identity:
                self.assertEqual(list(hit_indices(coeff, d, 0, c.cutoff + 1000,
                                                 start=c.cutoff)), [])

    def test_nonrigid(self):
        self.assertIsNone(rigid_certificate((1, 4), 2))
        self.assertIsNone(rigid_certificate((1, 0, 2), 2))

    def test_tamper_rejected(self):
        c = rigid_certificate((1, 0, 0, 0, 1), 2)
        from dataclasses import replace
        self.assertFalse(verify_certificate(replace(c, remainder_numerators=(0,))))
        self.assertFalse(verify_certificate(replace(c, cutoff=1)))

    def test_random_rigid_cutoffs(self):
        rng = random.Random(41577)
        for d in (2, 3, 4):
            for _ in range(30):
                q = rng.randrange(1, 3)
                b = rng.choice((-2, -1, 1, 2))
                f = [rng.randrange(-3, 4) for _ in range(d * q)] + [b ** d]
                cert = rigid_certificate(f, d)
                self.assertTrue(verify_certificate(cert), cert)
                if not cert.exact_identity and cert.cutoff <= 300:
                    self.assertEqual(list(hit_indices(f, d, 0, cert.cutoff + 100,
                                                      start=cert.cutoff)), [])

if __name__ == '__main__':
    unittest.main()
