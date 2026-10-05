import copy,json,unittest
from fractions import Fraction as Q
from math import comb,factorial,prod
from perfectpower.gamma_arithmetic import *
from perfectpower.core import integer_power_root


class GammaArithmeticTests(unittest.TestCase):
    def test_gamma_shift_exact_polynomial(self):
        r=normalize({'kind':'gamma_shift','a':2,'b':3,'shift':4})
        for n in range(20):self.assertEqual(evaluate(r['numerator'],n),prod(2*n+3+j for j in range(4)))
        self.assertTrue(verify_normalization(r))
        r['numerator']=(1,)
        self.assertFalse(verify_normalization(r))

    def test_binomial_small_indices_zero_and_denominator(self):
        for width in range(8):
            r=normalize({'kind':'binomial','width':width})
            for n in range(15):self.assertEqual(Q(evaluate(r['numerator'],n),r['denominator']),comb(n,width))

    def test_binomial_bounded_power_scan(self):
        r=analyze_expression({'kind':'binomial','width':2},interval=[-10,100])
        expected=[]
        for n in range(101):
            y=integer_power_root(comb(n,2),2)
            if y is not None:expected.extend((n,z) for z in sorted({y,-y}))
        self.assertEqual(r['bounded']['points'],expected)
        self.assertTrue(verify_gamma(json.loads(json.dumps(r))))

    def test_empty_natural_domain(self):
        r=analyze_expression({'kind':'gamma_shift','shift':3},interval=[-10,-1])
        self.assertEqual(r['bounded']['status'],'COMPLETE')
        self.assertEqual(r['bounded']['points'],[])
        self.assertTrue(verify_expression(r))

    def test_legendre_matches_integer_factorization(self):
        for n in range(40):
            for p in (2,3,5,7,11):
                value=factorial(n);e=0
                while value%p==0:value//=p;e+=1
                self.assertEqual(legendre(n,p)['exponent'],e)

    def test_prime_obstruction_without_factorial(self):
        r=factorial_power(10**100,[3],[1,1,1],2)
        self.assertEqual(r['factorials_constructed'],0)
        self.assertIn(r['status'],('NOT_POWER','UNRESOLVED'))
        self.assertTrue(verify_factorial_power(r))

    def test_central_infinite_family_zero_and_signs(self):
        r=analyze_gamma({'kind':'factorial_ratio','numerator':[2],'denominator':[1,1]},2,n=10**100)
        self.assertEqual(r['global']['points'],[(0,-1),(0,1)])
        self.assertEqual(r['point']['status'],'NOT_POWER')
        self.assertTrue(verify_gamma(r))
        self.assertEqual(factorial_power(0,[2],[1,1])['status'],'POWER')
        self.assertEqual(factorial_power(8,[2,3],[3,1,1])['proof']['kind'],'central_binomial')

    def test_all_prime_criterion_independent_small_ratios(self):
        families=[([3],[1,2]),([2,2],[1,1,1,1]),([1],[2]),([4],[2,2]),([1,1],[1,1])]
        for a,b in families:
            for n in range(12):
                value=Q(prod(factorial(c*n) for c in a),prod(factorial(c*n) for c in b))
                for d in (2,3,4):
                    r=factorial_power(n,a,b,d,complete=True)
                    expected=value.denominator==1 and integer_power_root(value.numerator,d) is not None
                    self.assertEqual(r['status']=='POWER',expected,(a,b,n,d,r))
                    self.assertNotEqual(r['status'],'UNRESOLVED')

    def test_landau_integral_and_nonintegral(self):
        for a,b,expected in [([2],[1,1],True),([3],[1,2],True),([1,1],[2],False),([],[],True)]:
            r=landau(a,b);self.assertEqual(r['integral_for_all_n'],expected);self.assertTrue(verify_landau(r))
        with self.assertRaises(ValueError):landau([3],[1])

    def test_hypergeometric_terms_match_factorials(self):
        for a,b in [([2],[1,1]),([3],[1,2]),([1,1],[2]),([],[])]:
            values=hypergeometric_terms(hypergeometric(a,b),20)
            expected=[str(Q(prod(factorial(c*n) for c in a),prod(factorial(c*n) for c in b))) for n in range(20)]
            self.assertEqual(values,expected)

    def test_units_match_stripped_factorials(self):
        for p in (2,3,5,7):
            for depth in (1,2,3):
                for n in range(35):
                    value=factorial(n);e=0
                    while value%p==0:value//=p;e+=1
                    r=factorial_unit(n,p,depth)
                    self.assertEqual(r['valuation'],e)
                    self.assertEqual(r['unit'],value%(p**depth))

    def test_ratio_unit_handles_noninvertible_original_denominator(self):
        r=ratio_unit(3,[2],[1,1],2,4)
        self.assertEqual((r['exponent'],r['unit']),(2,5))
        self.assertTrue(local_factorial_obstruction(3,[2],[1,1],2,2,4)['obstruction'])

    def test_no_false_local_obstruction_for_actual_powers(self):
        for n in range(20):
            for p in (2,3,5):
                self.assertFalse(local_factorial_obstruction(n,[2,2],[1,1,1,1],2,p,3)['obstruction'])

    def test_budgets_do_not_advertise_survival_as_power(self):
        r=factorial_power(1000000,[2,2],[1,1,1,1],2,complete=True,work_limit=100)
        self.assertEqual(r['status'],'UNRESOLVED')
        with self.assertRaises(WorkLimit):hypergeometric([4096],[4096])
        with self.assertRaises(WorkLimit):factorial_unit(5,7,8,work_limit=100)
        with self.assertRaises(ValueError):legendre(10,9)
        with self.assertRaises(ValueError):normalize({'kind':'gamma_shift','b':0,'shift':3})
        high=analyze_expression({'kind':'binomial','width':64},64,interval=[0,3])
        self.assertEqual(high['global_status'],'UNRESOLVED')
        self.assertTrue(verify_expression(high))
        zero=normalize({'kind':'rising','b':0,'width':3})
        self.assertEqual(evaluate(zero['numerator'],0),0)

    def test_scan_matches_direct_binomial_square(self):
        r=scan_factorial([2],[1,1],lo=0,hi=100)
        self.assertEqual(r['hits'],[0]);self.assertTrue(r['complete'])

    def test_replay_rejects_tampering(self):
        r=analyze_gamma({'kind':'factorial_ratio','numerator':[3],'denominator':[1,2]},n=5,complete=True)
        self.assertTrue(verify_gamma(json.loads(json.dumps(r))))
        r['point']['status']='POWER'
        self.assertFalse(verify_gamma(r))

    def test_public_factorial_binomial_and_multinomial_syntax(self):
        for spec in [{'kind':'factorial'},{'kind':'factorial','a':0},
                     {'kind':'central_binomial'},{'kind':'binomial_linear','top':2,'bottom':1},
                     {'kind':'multinomial','parts':[1,1,1]}]:
            r=analyze_gamma(spec,n=5,complete=True)
            self.assertTrue(verify_gamma(json.loads(json.dumps(r))))
        from perfectpower.arithmetic_engine import ArithmeticEngine
        self.assertEqual(ArithmeticEngine().analyze_gamma({'kind':'central_binomial'})['global']['status'],'COMPLETE')

    def test_unit_filter_beats_prime_list_and_boundary_retained(self):
        r=factorial_power(1,[101],[100])
        self.assertEqual(r['proof']['kind'],'unit_obstruction')
        self.assertEqual(r['factorials_constructed'],0)
        self.assertEqual(hypergeometric([],[])['generating_function_equation']['constant_boundary'],1)
        self.assertEqual(hypergeometric([2],[1,1])['generating_function_equation']['constant_boundary'],0)

    def test_huge_bounded_family_uses_global_theorem(self):
        r=analyze_gamma({'kind':'central_binomial'},interval=[0,10**100])
        self.assertEqual(r['bounded']['hits'],[0])
        self.assertEqual(r['bounded']['status'],'COMPLETE')
        self.assertTrue(verify_gamma(r))
        self.assertEqual(factorial_power(1,[1],[])['status'],'POWER')

    def test_unit_replay_and_tampering(self):
        r=local_factorial_obstruction(3,[2],[1,1],2,2,4)
        self.assertTrue(verify_local(json.loads(json.dumps(r))))
        self.assertTrue(verify_ratio_unit(r['ratio_unit']))
        self.assertTrue(verify_unit(r['ratio_unit']['numerator_units'][0]))
        r['obstruction']=False
        self.assertFalse(verify_local(r))

    def test_symbolic_period_and_finite_mellin(self):
        self.assertEqual(beta_period(4)['gamma_denominator'],'3/4')
        r=finite_mellin([1,2],3)
        self.assertEqual(r['integral'],'9/4')
        with self.assertRaises(ValueError):finite_mellin([0,1],3)
