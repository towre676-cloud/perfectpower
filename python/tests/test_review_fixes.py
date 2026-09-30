"""Regressions for three defects found in an external review: unregistered complete lists,
a linear-time cube root on large inputs, and floating-point Hessian reduction."""
import random
import sys
import time
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from perfectpower import thue_graph as G  # noqa: E402
from perfectpower.branch_descent import icbrt  # noqa: E402
from perfectpower.compiler import (COMPLETE_FINITE, PowerConstraint, _generated_complete,  # noqa: E402
                                   _icbrt, compile_constraint, mordell_complete)
from perfectpower.specialize import parse_poly  # noqa: E402


class RegisteredCompleteLists(unittest.TestCase):
    def test_all_generated_lists_registered(self):
        # 26 branch-compiler lists + 10 transported-Thue lists
        self.assertEqual(len(_generated_complete()), 36)
        self.assertEqual(mordell_complete(-56)[0], {18: [76]})
        self.assertIn('PerfectPower.DescentThue.complete_of_thue', mordell_complete(-56)[1])

    def test_compiler_reaches_them(self):
        for expr, hits in [('n**3 - 1', [(1, [0])]), ('n**3 - 29', []), ('n**3 - 56', [(18, [-76, 76])]),
                           ('n**3 - 92', []), ('(3*n + 15)**3 - 56', [(1, [-76, 76])])]:
            p = compile_constraint(PowerConstraint(parse_poly(expr), 2))
            self.assertEqual(p.status, COMPLETE_FINITE, expr)
            self.assertEqual(p.all_hits(), hits, expr)


class ExactCubeRoot(unittest.TestCase):
    def test_floor_and_speed(self):
        rng = random.Random(1)
        cases = list(range(-2000, 2000)) + [10 ** 45, 10 ** 45 - 1, 10 ** 600, -(10 ** 600) + 7]
        cases += [rng.randrange(-10 ** 400, 10 ** 400) for _ in range(500)]
        t = time.time()
        for f in (_icbrt, icbrt):
            for n in cases:
                r = f(n)
                self.assertTrue(r ** 3 <= n < (r + 1) ** 3, (f.__name__, n))
        self.assertLess(time.time() - t, 5)


class ExactHessianReduction(unittest.TestCase):
    def test_huge_unimodular_disguise(self):
        F = (1, 0, -1, 0)                                   # x^3 - x y^2
        H = G.compose(F, ((1, 10 ** 400), (0, 1)))          # x = u + 10^400 v, y = v
        c, T = G.canonical(H)
        self.assertEqual(G.compose(H, T), c)
        self.assertEqual(c, G.canonical(F)[0])


if __name__ == '__main__':
    unittest.main()
