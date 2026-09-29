import random
import unittest
from fractions import Fraction as Q
from continuation_tools.rational_yun import (
    ONE, add, mul, power, scale, poly, yun, evaluate, integer_root, rational_power)


class RationalYunTests(unittest.TestCase):
    def test_integer_coprimality_trap(self):
        f = mul((0, 1), power((2, 1), 2))
        self.assertEqual(yun(f).layers, ((1, poly((0, 1))), (2, poly((2, 1)))))

    def test_constant_and_zero(self):
        for c in [-17, 1, Q(3, 7)]:
            self.assertEqual(yun((c,)).layers, ())
        with self.assertRaises(ValueError):
            yun((0, 0))

    def test_sparse_multiplicities_and_rational_roots(self):
        a, b = poly((Q(-1, 3), 1)), poly((Q(2, 5), 1))
        f = scale(mul(power(a, 3), power(b, 7)), Q(-11, 13))
        self.assertEqual(yun(f).layers, ((3, a), (7, b)))

    def test_irreducible_and_linear_mixture(self):
        a, b = poly((1, 0, 1)), poly((-2, 1))
        f = mul(power(a, 4), power(b, 2))
        self.assertEqual(yun(f).layers, ((2, b), (4, a)))

    def test_seeded_reconstruction_and_splits(self):
        rng = random.Random(676)
        samples = []
        for _ in range(80):
            samples.append(poly([rng.randint(-5, 5) for _ in range(rng.randint(1, 9))]))
        for _ in range(40):
            f = (Q(rng.choice([-3, 1, 2])),)
            roots = rng.sample(range(-5, 6), 3)
            for r in roots:
                f = mul(f, power((-r, 1), rng.randint(1, 5)))
            samples.append(f)
        for f in samples:
            if not f:
                continue
            y = yun(f)
            self.assertTrue(y.verify(f))
            for d in range(2, 9):
                g, r = y.split(d)
                self.assertEqual(scale(mul(r, power(g, d)), y.lead), f)
                # Actual integer-root test against the stripped rational factor.
                for n in range(-8, 9):
                    value = evaluate(f, n)
                    if value.denominator != 1:
                        continue
                    hit = integer_root(value.numerator, d) is not None
                    reduced = value == 0 or rational_power(y.lead * evaluate(r, n), d)
                    self.assertEqual(hit, reduced, (f, d, n))

    def test_zero_factors_are_hits(self):
        f = scale(power((-2, 1), 2), 3)
        y = yun(f)
        _, r = y.split(2)
        self.assertFalse(rational_power(y.lead * evaluate(r, 2), 2))
        self.assertEqual(integer_root(int(evaluate(f, 2)), 2), 0)

    def test_signed_root_and_large_exactness(self):
        for d in range(2, 12):
            for x in [0, 1, 2, 12345678901234567890]:
                self.assertEqual(integer_root(x ** d, d), x)
                if x > 1:
                    self.assertIsNone(integer_root(x ** d + 1, d))
            self.assertEqual(integer_root(-8, 3), -2)
            self.assertIsNone(integer_root(-4, 2))

    def test_denominator_clearing_with_exceptional_zero(self):
        for d, r, c in [(3, 1, 2), (4, 3, 8), (2, 1, 2)]:
            for n in range(-100, 101):
                value = Q(c) * (Q(n) - Q(1, 2)) ** r * (n - 3) ** d
                self.assertEqual(value.denominator, 1)
                residual = c * 2 ** (d - r) * (2 * n - 1) ** r
                self.assertEqual(integer_root(value.numerator, d) is not None,
                                 value == 0 or integer_root(residual, d) is not None)

    def test_two_square_branches(self):
        # F=4(x²-2)² is a fourth power iff +2(x²-2) or -2(x²-2) is a square.
        f = scale(power((-2, 0, 1), 2), 4)
        for n in range(-300, 301):
            w = n * n - 2
            self.assertEqual(integer_root(int(evaluate(f, n)), 4) is not None,
                             rational_power(2 * w, 2) or rational_power(-2 * w, 2))
        self.assertTrue(rational_power(0, 2) and rational_power(-Q(0), 2))


if __name__ == '__main__':
    unittest.main()
