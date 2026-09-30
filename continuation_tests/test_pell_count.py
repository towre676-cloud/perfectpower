"""Theorem C as a count (`Decomposition.pell_count`): brute-force hit counts of Pell-type
polynomials stay within a bounded distance of kappa * log N.  The cases cover a populated branch,
a full-square factor vanishing at an integer, d = 4 with the two roots +-gamma of gamma^2 = lc,
a negative leading branch, a square leading coefficient (bounded), and an unpopulated class."""
import math
import unittest

from continuation_tests.test_radical_count import is_power, mul, power, value
from perfectpower.atlas import classify

CASES = [
    ('2n^2+1', [1, 0, 2], 2),
    ('(2n^2+1)(n-3)^2, zero at n=3', mul([1, 0, 2], power([-3, 1], 2)), 2),
    ('4(n^2+1)^2, d=4, branches +-2', mul([4], power([1, 0, 1], 2)), 4),
    ('-(n^2-7), negative', [7, 0, -1], 2),
    ('9(n^2+1), square leading coefficient', [9, 0, 9], 2),
    ('3(n^2-2)(n-1)^2, unpopulated', mul([3], mul([-2, 0, 1], power([-1, 1], 2))), 2),
]


class PellCount(unittest.TestCase):
    def test_bounded_discrepancy(self):
        checkpoints = (10, 100, 1000, 10000, 100000, 1000000)
        for name, f, d in CASES:
            c = classify(f, d)
            self.assertEqual(c.kind, 'pell', name)
            kappa = c.details.get('kappa', 0.0)
            count, worst = 0, 0.0
            for n in range(1, checkpoints[-1] + 1):
                if is_power(value(f, n), d):
                    count += 1
                if n in checkpoints:
                    worst = max(worst, abs(count - kappa * math.log(n)))
            self.assertLess(worst, 4, (name, kappa, count))

    def test_some_branch_is_populated(self):
        populated = [name for name, f, d in CASES if classify(f, d).details.get('kappa', 0) > 0]
        self.assertGreaterEqual(len(populated), 3, populated)

    def test_explicit_constant(self):
        # `PellExact.Kpell`: one branch A n^2 + B n + C with a unit (u, v) of X^2 - 4A Y^2 = 1
        def kpell(A, B, C, u, v):
            delta = abs(B * B - 4 * A * C)
            z = delta * (1 + u * u)
            w = (2 * z + 2) * (1 + math.sqrt(4 * A))
            log_eps = math.log(u + v * math.sqrt(4 * A))
            kc = 3 + (2 * math.log(w + delta) + math.log(2 + math.sqrt(delta)) + math.log(2)) / log_eps
            return (abs(B) + 1 + (2 * z + 3) ** 2 * (2 * A) ** 2 * kc
                    + (2 * z + 3) ** 2 / log_eps * math.log(2 * A + abs(B)))
        # 2n^2 + 1 is the branch (A, B, C) = (2, 0, 1), unit (3, 1) of X^2 - 8Y^2 = 1
        f = [1, 0, 2]
        kappa = classify(f, 2).details['kappa']
        bound = kpell(2, 0, 1, 3, 1)
        count = 0
        for n in range(1, 100001):
            if is_power(value(f, n), 2):
                count += 1
            self.assertLessEqual(abs(count - kappa * math.log(n)), bound)
        self.assertTrue(math.isfinite(bound) and bound > 0)


if __name__ == '__main__':
    unittest.main()
