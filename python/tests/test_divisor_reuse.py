import random
import unittest
from fractions import Fraction as Q
from math import isqrt

from perfectpower.divisor_square import (Budget, WorkLimit, evaluate, integer_roots,
                                        match_square_plus_constant, solve, emit_lean)
from perfectpower.compiler import PowerConstraint, compile_constraint, ppow, padd
from perfectpower.quotient_algebra import QuotientAlgebra
from perfectpower.local_quartic import primitive_residue_certificate, chart_polynomials


class DivisorSquare(unittest.TestCase):
    def test_against_independent_coordinate_scan(self):
        rng = random.Random(20261004)
        for _ in range(150):
            as_ = [rng.randint(-4, 4) for _ in range(rng.randint(2, 7))]
            as_[-1] = rng.choice([-3, -2, -1, 1, 2, 3])
            k = rng.choice([i for i in range(-15, 16) if i])
            # Prior Lean-proved rectangular bounds, independently scanned here.
            bound = sum(map(abs, as_))+abs(k)+1
            expected = []
            for x in range(-bound, bound+1):
                t = evaluate(as_, x)**2+k
                if t >= 0 and isqrt(t)**2 == t:
                    expected.extend((x, y) for y in sorted({-isqrt(t), isqrt(t)}))
            self.assertEqual(solve(as_, k)['points'], sorted(expected), (as_, k))

    def test_roots_shifts_and_repetitions(self):
        self.assertEqual(integer_roots([0, 0, 2, -3, 1]), [0, 1, 2])
        self.assertEqual(integer_roots([4, -4, 1]), [2])
        r = solve([1000000, 1], 1)
        self.assertEqual(r['points'], [(-1000000, -1), (-1000000, 1)])
        self.assertEqual(r['divisor_trials'], 1001)
        self.assertFalse(r['execution_verified'])

    def test_exact_recognition_and_compiler(self):
        for q in ((-1000000, 1), (3, -2, 5), (0, 0, -2), (4, -4, 1)):
            for k in (-7, 1, 8):
                f = padd(ppow(q, 2), (k,))
                match = match_square_plus_constant(f)
                self.assertIsNotNone(match)
                self.assertEqual(padd(ppow(match[0], 2), (match[1],)), f)
        p = compile_constraint(PowerConstraint((1000000000001, -2000000, 1), 2))
        self.assertEqual(list(p.iter_hits(2000000)), [(1000000, [-1, 1])])
        self.assertIn('factor pairs', p.method)
        self.assertIsNone(match_square_plus_constant([1, 0, 2]))

    def test_no_silent_partial_results(self):
        with self.assertRaises(WorkLimit):
            solve([1000000, 1], 1, work_limit=10)
        for coefficients, k in (([1], 1), ([1, 0], 1), ([0, 1], 0)):
            with self.assertRaises(ValueError):
                solve(coefficients, k)
        with self.assertRaises(ValueError):
            solve([0.5, 1], 1)
        with self.assertRaises(ValueError):
            emit_lean([0, 1], 1, 'x; bad')


class QuotientArithmetic(unittest.TestCase):
    def test_quadratic_norm_and_inverse(self):
        a = QuotientAlgebra((-2, 0, 1))
        theta = a.element((0, 1))
        self.assertEqual(theta**2, a.element(2))
        z = a.element((3, 2))
        self.assertEqual(z.norm(), Q(1))
        self.assertEqual(z.trace(), Q(6))
        self.assertEqual(z.inverse(), a.element((3, -2)))

    def test_cubic_norm_and_cayley_hamilton(self):
        a = QuotientAlgebra((-2, 0, 0, 1))
        z = a.element((1, 1))
        self.assertEqual(z.norm(), 3)
        self.assertEqual(z.characteristic_polynomial(), (Q(-3), Q(3), Q(-3), Q(1)))
        rng = random.Random(18)
        for degree in range(2, 7):
            a = QuotientAlgebra(tuple(rng.randrange(-3, 4) for _ in range(degree))+(1,))
            for _ in range(8):
                z = a.element(tuple(rng.randrange(-3, 4) for _ in range(degree)))
                w = a.element(tuple(rng.randrange(-3, 4) for _ in range(degree)))
                self.assertEqual((z*w).norm(), z.norm()*w.norm())
                self.assertEqual((z+w).trace(), z.trace()+w.trace())
                evaluated = a.element(0)
                for c in reversed(z.characteristic_polynomial()):
                    evaluated = evaluated*z+c
                self.assertEqual(evaluated, a.element(0))
                if z.norm():
                    self.assertEqual(z*z.inverse(), a.element(1))

    def test_zero_divisors_not_called_fields(self):
        a = QuotientAlgebra((-1, 0, 1))
        z = a.element((-1, 1))
        self.assertEqual(z.norm(), 0)
        with self.assertRaises(ZeroDivisionError):
            z.inverse()
        self.assertFalse(z.receipt()['irreducibility_certified'])
        with self.assertRaises(ValueError):
            z + QuotientAlgebra((-2, 0, 1)).element(1)


class QuarticResidues(unittest.TestCase):
    def test_obstruction_and_survivor_boundary(self):
        self.assertTrue(primitive_residue_certificate(2, 1, 2, 3)['obstructed'])
        self.assertFalse(primitive_residue_certificate(1, 0, 1, 3)['obstructed'])
        for p in (0, 1, 4, 9):
            with self.assertRaises(ValueError):
                primitive_residue_certificate(2, 1, 2, p)

    def test_nonunit_chart_substitutes_polynomial(self):
        d, A, c, p = 2, 7, 3, 5
        first, second = chart_polynomials(d, A, c, p)
        for t in range(-10, 11):
            self.assertEqual(evaluate(first, t), d*t**4+A*t*t+c)
            self.assertEqual(evaluate(second, t), d+A*(p*t)**2+c*(p*t)**4)
        with self.assertRaises(ValueError):
            primitive_residue_certificate(2, 1, 2, 101, max_work=100)


if __name__ == '__main__':
    unittest.main()
