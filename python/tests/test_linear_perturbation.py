import random
import unittest
from math import isqrt
from perfectpower.linear_perturbation import match,solve,emit_lean,match_square_leading,solve_square_leading
from perfectpower.divisor_square import WorkLimit
from perfectpower.compiler import compile_constraint,PowerConstraint,COMPLETE_FINITE


def expanded(L,a,b,c,d):return [b*b+d,2*a*b+c,a*a+2*L*b,2*L*a,L*L]


class LinearPerturbationTests(unittest.TestCase):
    def test_random_complete_against_independent_interval(self):
        rng=random.Random(420)
        for _ in range(500):
            L=rng.choice([-3,-2,-1,1,2,3]);a,b,c,d=[rng.randrange(-6,7) for _ in range(4)]
            if (c,d)==(0,0):d=1
            result=solve(L,a,b,c,d)
            independent=[]
            for x in range(-100,101):
                n=(L*x*x+a*x+b)**2+c*x+d
                if n>=0 and isqrt(n)**2==n:
                    independent.extend((x,y) for y in sorted({isqrt(n),-isqrt(n)}))
            self.assertEqual(result['points'],independent)

    def test_zero_perturbation_fibre(self):
        self.assertIn((-1,0),solve(1,0,-1,2,2)['points'])
        self.assertEqual(solve(1,0,0,2,1)['points'],[(-1,0),(0,-1),(0,1),(1,-2),(1,2)])

    def test_recognizer_round_trip(self):
        for L in [1,2,7]:
            p=(L,-3,2,5,-4)
            self.assertEqual(match(expanded(*p)),p)
        self.assertIsNone(match([0,0,0,0,1]))
        self.assertIsNone(match([1,1,0,0,2]))
        self.assertIsNone(match([1,1,1,0,1]))

    def test_budget_and_infinite_rejection(self):
        with self.assertRaises(WorkLimit):solve(1,0,0,100,1,work_limit=10)
        with self.assertRaises(ValueError):solve(1,0,0,0,0)
        with self.assertRaises(ValueError):solve(0,0,0,1,1)

    def test_large_leading_coefficient(self):
        result=solve(10**40,0,0,1,1)
        self.assertEqual(result['coordinate_bound'],3)
        self.assertEqual(result['points'],[(-1,-10**40),(-1,10**40),(0,-1),(0,1)])

    def test_compiler_complete_positive_domain(self):
        plan=compile_constraint(PowerConstraint(expanded(1,0,0,2,1),2))
        self.assertEqual(plan.status,COMPLETE_FINITE)
        self.assertEqual(plan.all_hits(),[(1,[-2,2])])
        self.assertIn('LinearPerturbation.complete',' '.join(plan.justification))

    def test_fractional_completion_and_compiler(self):
        f=[1,1,1,1,1]
        self.assertIsNone(match(f))
        self.assertEqual(match_square_leading(f),(1,1,1,1,1))
        result=solve_square_leading(1,1,1,1,1)
        self.assertEqual(result['points'],[(-1,-1),(-1,1),(0,-1),(0,1),(3,-11),(3,11)])
        plan=compile_constraint(PowerConstraint(f,2))
        self.assertEqual(plan.status,COMPLETE_FINITE)
        self.assertIn((3,[-11,11]),plan.all_hits())
        self.assertIn('SquareLeadingQuartic.complete',' '.join(plan.justification))

    def test_raw_random_complete(self):
        rng=random.Random(64)
        for _ in range(100):
            u,v,w,z=[rng.randrange(-3,4) for _ in range(4)]
            if match_square_leading([z,w,v,u,1]) is None:continue
            result=solve_square_leading(1,u,v,w,z)
            expected=[]
            for x in range(-2000,2001):
                n=x**4+u*x**3+v*x*x+w*x+z
                if n>=0 and isqrt(n)**2==n:
                    expected.extend((x,y) for y in sorted({isqrt(n),-isqrt(n)}))
            self.assertEqual(result['points'],expected)

    def test_emitter(self):
        self.assertIn('native_linear_perturbation',emit_lean(1,0,0,2,1))
        with self.assertRaises(ValueError):emit_lean(1,0,0,2,1,name='bad-name')


if __name__=='__main__':unittest.main()
