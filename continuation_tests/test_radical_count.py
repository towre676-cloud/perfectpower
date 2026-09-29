"""Theorem B as a count (`Decomposition.radical_count`): brute-force hit counts of radical-type
polynomials stay within a bounded distance of kappa * N^(1/t), including exceptional zeros,
negative coefficients (odd and even d), negative shifts and the unsolvable (kappa = 0) case."""
import unittest

from perfectpower.atlas import classify


def mul(f, g):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return out


def power(f, e):
    out = [1]
    for _ in range(e):
        out = mul(out, f)
    return out


def is_power(x, d):
    if x < 0:
        if d % 2 == 0:
            return False
        x = -x
    r = round(abs(x) ** (1.0 / d)) if x else 0
    return any(k >= 0 and k ** d == x for k in (r - 1, r, r + 1))


def value(f, n):
    return sum(c * n ** i for i, c in enumerate(f))


CASES = [
    # (description, coefficients low-to-high, d)
    ('(2n-3)(n-5)^2, zero at n=5', mul([-3, 2], power([-5, 1], 2)), 2),
    ('-(n+7)(n+1)^3, odd d, negative coefficient', mul([-7, -1], power([1, 1], 3)), 3),
    ('-(n+2) n^2, even d, negative coefficient', mul([-2, -1], power([0, 1], 2)), 2),
    ('2(n-3)^2 with d=4, unsolvable', mul([2], power([-3, 1], 2)), 4),
    ('3(n+11), shift', [33, 3], 2),
]


class RadicalCount(unittest.TestCase):
    def test_bounded_discrepancy(self):
        for name, f, d in CASES:
            c = classify(f, d)
            self.assertEqual(c.kind, 'radical', name)
            kappa = c.details.get('kappa', 0.0) if c.details.get('solvable', True) else 0.0
            t = c.details['t']
            count, worst = 0, 0.0
            for n in range(1, 200001):
                if is_power(value(f, n), d):
                    count += 1
                if n in (10, 100, 1000, 10000, 100000, 200000):
                    worst = max(worst, abs(count - kappa * n ** (1.0 / t)))
            self.assertLess(worst, 12, (name, kappa, t, count))


if __name__ == '__main__':
    unittest.main()
