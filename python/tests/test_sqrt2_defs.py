"""Independent integer oracles for the four `SqrtTwoDefs` entries (finite evidence only; the Lean
theorems in `PerfectPower/SqrtTwoDefs.lean` are the proofs)."""
import sys
import unittest
from fractions import Fraction
from itertools import product
from math import comb, isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.oeis_orbit import _A, _B  # noqa: E402
from perfectpower.oeis_source import SeqDir, parse_seq  # noqa: E402

DATA = ROOT / 'data' / 'oeis'


def good(cols):
    """Exhaustive reachability on the 2 x n grid (cells (row, col)), paths in all directions."""
    n = len(cols)
    on = {(r, j) for j, c in enumerate(cols) for r in (0, 1) if c[r]}
    if (0, 0) not in on:
        return False
    seen, stack = {(0, 0)}, [(0, 0)]
    while stack:
        r, j = stack.pop()
        for y in ((1 - r, j), (r, j - 1), (r, j + 1)):
            if y in on and y not in seen:
                seen.add(y)
                stack.append(y)
    return any((r, n - 1) in seen for r in (0, 1))


class TestSqrtTwoDefs(unittest.TestCase):
    def test_floor_recursion(self):
        # a(n) = floor(a(n-1) (1 + sqrt 2)), exactly: floor(a sqrt 2) = isqrt(2 a^2)
        a = 1
        for n in range(60):
            self.assertEqual(2 * a, _A(n + 1) + 1)
            a = a + isqrt(2 * a * a)

    def test_binomial_transform(self):
        c = lambda j: 1 if j == 0 else (0 if j % 2 else 2 ** (j // 2 - 1))   # noqa: E731
        for n in range(60):
            self.assertEqual(2 * sum(comb(n, j) * c(j) for j in range(n + 1)), _A(n) + 1)

    def test_reduced_numerators(self):
        r = Fraction(0)
        for n in range(1, 60):
            self.assertEqual(r.numerator, 2 * _B(n - 1))
            r = (r + 2) / (r + 1)

    def test_arrays_exhaustive(self):
        cols = [(a, b) for a in (0, 1) for b in (0, 1)]
        for n in range(1, 9):
            count = sum(good(arr) for arr in product(cols, repeat=n))
            self.assertEqual(count, _B(n + 1), n)

    def test_A018905_shift(self):
        src = SeqDir(DATA)
        dup = dict(parse_seq(src.text('A018905')).indexed())
        tgt = dict(parse_seq(src.text('A024537')).indexed())
        self.assertNotEqual(dup[0], tgt[0])                      # the label fails at the same index
        self.assertTrue(all(tgt[n + 1] == v for n, v in dup.items()))


if __name__ == '__main__':
    unittest.main()
