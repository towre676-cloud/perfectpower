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


if __name__ == '__main__':
    unittest.main()
