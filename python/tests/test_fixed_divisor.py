import math
import random
import unittest
from perfectpower.fixed_divisor import fixed_divisor,admissibility,generalized_choose,native_certificate,repeated_power_free,native_repeated_power_free
from perfectpower.power_free_local import local_admissibility
from perfectpower.divisor_square import WorkLimit
from perfectpower.query_service import dispatch


def eval_poly(f,x):
    v=0
    for a in reversed(f):v=a+x*v
    return v


class FixedDivisorTests(unittest.TestCase):
    def test_repeated_factor_obstruction(self):
        p=admissibility([0,0,1,-2,1])
        self.assertEqual(p['fixed_divisor'],4)
        self.assertFalse(p['locally_admissible'])
        self.assertEqual(p['fixed_divisor_prime'],2)
        self.assertTrue(admissibility([0,0,1,-2,1],exponent=3)['locally_admissible'])

    def test_repeated_admissible(self):
        self.assertTrue(admissibility([1,0,2,0,1])['locally_admissible'])
        with self.assertRaises(ValueError):local_admissibility([1,0,2,0,1])

    def test_zero_and_constants(self):
        self.assertEqual(fixed_divisor([0])['fixed_divisor'],0)
        self.assertFalse(admissibility([0],exponent=1024)['locally_admissible'])
        self.assertTrue(admissibility([-1])['locally_admissible'])
        self.assertFalse(admissibility([-12])['locally_admissible'])
        self.assertTrue(admissibility([-12],exponent=3)['locally_admissible'])

    def test_content_is_not_fixed_divisor(self):
        p=fixed_divisor([0,-1,1])
        self.assertEqual(p['fixed_divisor'],2)
        self.assertEqual(p['primitive_binomial_coefficients'],[0,0,1])
        self.assertTrue(admissibility([0,-1,1])['locally_admissible'])
        self.assertFalse(admissibility([0,-1,1],exponent=1)['locally_admissible'])

    def test_progression(self):
        self.assertEqual(fixed_divisor([1,0,1])['fixed_divisor'],1)
        self.assertEqual(fixed_divisor([1,0,1],start=1,step=2)['fixed_divisor'],2)
        self.assertEqual(fixed_divisor([1,0,1],start=1,step=-2)['fixed_divisor'],2)
        self.assertFalse(admissibility([1,0,1],exponent=1,start=1,step=2)['locally_admissible'])
        self.assertTrue(admissibility([1,0,1],exponent=2,start=1,step=2)['locally_admissible'])

    def test_constant_progression(self):
        p=fixed_divisor([-4,0,1],start=2,step=0)
        self.assertEqual((p['degree'],p['sample_values'],p['fixed_divisor']),(0,[0],0))

    def test_signed_newton_and_gcd_identity(self):
        rng=random.Random(90210)
        for _ in range(120):
            f=[rng.randint(-9,9) for _ in range(rng.randrange(1,10))]
            start,step=rng.randint(-10,10),rng.randint(-4,4)
            p=fixed_divisor(f,start=start,step=step);D=p['fixed_divisor']
            self.assertEqual(sum(a*b for a,b in zip(p['sample_values'],p['sample_bezout_weights'])),D)
            for n in [-101,-9,-1,0,1,12,10**12]:
                y=eval_poly(f,start+step*n)
                self.assertEqual(sum(c*generalized_choose(n,i) for i,c in enumerate(p['forward_differences'])),y)
                if D:
                    self.assertEqual(y%D,0)
                    self.assertEqual(sum(c*generalized_choose(n,i) for i,c in enumerate(p['primitive_binomial_coefficients'])),y//D)
                else:self.assertEqual(y,0)

    def test_translate_invariance(self):
        f=[-25,11,-2,3,1]
        D=fixed_divisor(f)['fixed_divisor']
        for a in [-10**20,-3,0,8,10**20]:self.assertEqual(fixed_divisor(f,start=a)['fixed_divisor'],D)

    def test_degree_plus_one_is_necessary(self):
        self.assertEqual([eval_poly([0,2,-3,1],n) for n in range(3)],[0,0,0])
        self.assertEqual(fixed_divisor([0,2,-3,1])['fixed_divisor'],6)

    def test_independent_local_enumeration(self):
        for f in [[0,-1,1],[0,0,1,-2,1],[1,0,2,0,1],[-12],[0],[2,2,2],[0,2,-3,1]]:
            D=fixed_divisor(f)['fixed_divisor']
            for p in [2,3,5,7]:
                for k in [1,2,3]:
                    q=p**k
                    self.assertEqual(all(eval_poly(f,n)%q==0 for n in range(q)),D%q==0)

    def test_prime_witnesses(self):
        p=admissibility([0,2,-3,1],exponent=2)
        for row in p['valuation_rows']:
            self.assertNotEqual(row['witness_value']%(row['prime']**2),0)

    def test_large_prime_and_exponent(self):
        p=admissibility([10007**2],exponent=2)
        self.assertEqual(p['fixed_divisor_prime'],10007)
        self.assertTrue(admissibility([10007**2],exponent=1024)['locally_admissible'])

    def test_budget_failure_never_partial(self):
        with self.assertRaises(WorkLimit):admissibility([1000003*1000033],factor_limit=1)
        # Exact fixed divisor itself needs no factorization.
        self.assertEqual(fixed_divisor([1000003*1000033])['fixed_divisor'],1000003*1000033)
        with self.assertRaises(WorkLimit):fixed_divisor([1]*130)
        with self.assertRaises(WorkLimit):native_certificate([1]*34)

    def test_input_validation(self):
        for f in [[],[True],[1.0],'x']:
            with self.assertRaises(ValueError):fixed_divisor(f)
        for k in [0,-1,True,1025]:
            with self.assertRaises(ValueError):admissibility([1],exponent=k)
        with self.assertRaises(ValueError):fixed_divisor([1],step=True)

    def test_native_packets(self):
        for f in [[0],[1],[0,0,1,-2,1],[1,0,2,0,1]]:
            p=native_certificate(f)
            self.assertFalse(p['lean']['kernel_checked'])
            self.assertNotIn('sorry',p['lean']['source'])
            self.assertNotIn('native_decide',p['lean']['source'])

    def test_query_service(self):
        for op in ['fixed_divisor','fixed_divisor_admissibility','native_fixed_divisor_certificate']:
            p=dispatch(None,{'op':op,'args':{'coefficients':[0,-1,1]}})
            self.assertEqual(p['fixed_divisor'],2)


class RepeatedPowerFreeTests(unittest.TestCase):
    def test_local_without_global(self):
        f=[4,0,4,0,1]
        self.assertTrue(admissibility(f)['locally_admissible'])
        self.assertEqual(repeated_power_free(f)['solutions'],[])

    def test_complete_finite_solutions(self):
        for f,expected in [([1,0,2,0,1],[0]),([0,0,1],[-1,1]),([0,0,-1],[-1,1]),([0,0,3],[-1,1]),([0,0,12],[]),([0,0,1,1],[1])]:
            p=repeated_power_free(f)
            self.assertEqual(p['solutions'],expected)
            self.assertEqual(p['global_density'],0)

    def test_cubic_and_signed(self):
        self.assertEqual(repeated_power_free([-8,12,-6,1],exponent=3)['solutions'],[1,3])
        self.assertEqual(repeated_power_free([8,-12,6,-1],exponent=3)['solutions'],[1,3])

    def test_primitive_nonmonic_factor(self):
        p=repeated_power_free([1,4,4]);self.assertEqual(p['repeated_factor'],[1,2]);self.assertEqual(p['solutions'],[-1,0])

    def test_noninteger_unit_fibres(self):
        p=repeated_power_free([4,0,8,0,4]);self.assertEqual(p['solutions'],[])

    def test_no_repeated_factor_route(self):
        for f in [[1],[0],[1,0,1]]:
            with self.assertRaises(ValueError):repeated_power_free(f)
        with self.assertRaises(ValueError):repeated_power_free([0,0,1],exponent=1)

    def test_native_root_budget(self):
        with self.assertRaises(WorkLimit):native_repeated_power_free([(10**6)**2,2*10**6,1],divisor_limit=1)

    def test_service(self):
        for op in ['repeated_power_free','native_repeated_power_free']:
            p=dispatch(None,{'op':op,'args':{'coefficients':[4,0,4,0,1]}})
            self.assertEqual(p['solutions'],[])
