"""The host-solver adapter (`perfectpower.smt_adapter`).  Skipped when z3-solver is not installed."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

try:
    import z3
except ImportError:  # optional dependency
    z3 = None


@unittest.skipIf(z3 is None, 'z3-solver not installed')
class Adapter(unittest.TestCase):
    def setUp(self):
        from perfectpower.smt_adapter import reduce_assertions, reduce_smt2
        self.reduce_assertions, self.reduce_smt2 = reduce_assertions, reduce_smt2
        self.n, self.m, self.w = z3.Ints('n m w')

    def test_replaces_solved_curve_over_all_integers(self):
        n, m = self.n, self.m
        x = 3 * n + 15
        r = self.reduce_assertions([m * m == x * x * x - 56])
        self.assertEqual(len(r.replacements), 1)
        self.assertEqual(r.replacements[0].solutions, [(1, -76), (1, 76)])
        self.assertIn('PerfectPower.Generated.MordellThue.minus56', r.replacements[0].lean)

    def test_negative_n_kept(self):
        # y^2 = x^3 - 20 has (6, +-14); x = n + 10 gives n = -4 (no n >= 1 domain here)
        n, m = self.n, self.m
        x = n + 10
        r = self.reduce_assertions([x * x * x - 20 == m * m])
        self.assertEqual(r.replacements[0].solutions, [(-4, -14), (-4, 14)])

    def test_no_points_becomes_false(self):
        n, m, w = self.n, self.m, self.w
        r = self.reduce_assertions([z3.And(m * m == (2 * n + 1) ** 3 - 5, w > n)])
        self.assertEqual(len(r.replacements), 1)
        s = z3.Solver()
        s.add(r.assertions)
        self.assertEqual(s.check(), z3.unsat)

    def test_unrecognized_left_unchanged(self):
        n, m, w = self.n, self.m, self.w
        orig = [m * m == n * n * n + n + 1, w * w == n]
        r = self.reduce_assertions(orig)
        self.assertEqual(r.replacements, [])
        self.assertEqual([str(a) for a in r.assertions], [str(a) for a in orig])

    def test_smt2_text(self):
        r = self.reduce_smt2('(declare-const n Int)(declare-const m Int)'
                             '(assert (= (* m m) (- (* n n n) 1)))')
        self.assertEqual(r.replacements[0].solutions, [(1, 0)])

    def test_bounded_pell_pairs_equal_square(self):
        # N(N-1)/2 = S^2 with explicit bounds: the exact orbit solutions, checked by brute force
        from math import isqrt
        N, S = z3.Ints('N S')
        r = self.reduce_assertions([N * (N - 1) == 2 * S * S, N >= -3000, N < 3001], allow_unchecked=True)
        self.assertEqual(r.replacements[0].evidence, 'python_enumeration_unchecked')
        self.assertEqual(self.reduce_assertions([N * (N - 1) == 2 * S * S, N >= -3000, N < 3001]).replacements, [])
        self.assertEqual(len(r.replacements), 1)
        brute = sorted({(n, sg * y) for n in range(-3000, 3001) for y in [isqrt(max(n * (n - 1) // 2, 0))]
                        for sg in (1, -1) if 2 * y * y == n * (n - 1)})
        self.assertEqual(r.replacements[0].solutions, brute)

    def test_unbounded_pell_left_to_host(self):
        N, S = z3.Ints('N S')
        r = self.reduce_assertions([N * (N - 1) == 2 * S * S, N >= 1], allow_unchecked=True)
        self.assertEqual(r.replacements, [])


if __name__ == '__main__':
    unittest.main()
