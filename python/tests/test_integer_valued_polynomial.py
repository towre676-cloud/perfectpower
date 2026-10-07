from fractions import Fraction as Q
import hashlib
import math
import random
import unittest
from perfectpower.integer_valued_polynomial import normalize,analyze,gamma_packet,native_certificate
from perfectpower.query_service import dispatch
from perfectpower.divisor_square import WorkLimit


def ev(f,x):
    v=0
    for c in reversed(f):v=v*x+c
    return v


class IntegerValuedTests(unittest.TestCase):
    def test_normalization(self):
        self.assertEqual(normalize(['2/4','3/6',0]),([1,1],2,['1/2','1/2']))
    def test_denominator_cancellation(self):
        p=analyze([0,'-1/2','1/2'],exponent=1)
        self.assertTrue(p['integral_everywhere'])
        self.assertEqual((p['numerator_fixed_divisor'],p['integer_domain_fixed_divisor']),(2,1))
        self.assertTrue(p['locally_admissible_on_integer_domain'])
    def test_partial_domain(self):
        p=analyze(['1/2',0,'1/2'])
        self.assertEqual(p['integral_residues'],[1])
        self.assertEqual(p['charts'][0]['coefficients'],[1,2,2])
        self.assertEqual(p['integer_domain_fixed_divisor'],1)
    def test_partial_obstruction(self):
        p=analyze(['7/2',0,'1/2'])
        self.assertEqual(p['integer_domain_fixed_divisor'],4)
        self.assertEqual(p['obstruction_prime'],2)
        self.assertFalse(p['locally_admissible_on_integer_domain'])
    def test_many_charts(self):
        p=analyze([0,'1/6','1/6'])
        self.assertEqual(p['integral_residues'],[0,2,3,5])
        self.assertEqual(len(p['charts']),4)
    def test_empty_domain(self):
        p=analyze(['1/2'],interval=[-100,100])
        self.assertTrue(p['integral_domain_empty'])
        self.assertEqual((p['integer_domain_fixed_divisor'],p['integral_input_count']),(0,0))
        self.assertFalse(p['locally_admissible_on_integer_domain'])
    def test_zero_and_signed_constant(self):
        self.assertFalse(analyze([0])['locally_admissible_on_integer_domain'])
        self.assertFalse(analyze([-12])['locally_admissible_on_integer_domain'])
        self.assertTrue(analyze([-12],exponent=3)['locally_admissible_on_integer_domain'])
    def test_value_lattice_is_distinct(self):
        p=analyze(['7/2',0,'1/2'])
        self.assertEqual(p['rational_value_lattice'],'1/2')
        self.assertEqual(p['integer_domain_fixed_divisor'],4)
    def test_signed_chart_identity(self):
        for cs in [['1/2',0,'1/2'],[0,'1/6','1/6'],[0,0,'1/3']]:
            p=analyze(cs);F,L=p['numerator'],p['denominator']
            for chart in p['charts']:
                for n in [-10**30,-20,-1,0,1,21,10**30]:
                    self.assertEqual(ev(F,chart['residue']+L*n),L*ev(chart['coefficients'],n))
    def test_interval_counts(self):
        for cs in [['1/2',0,'1/2'],[0,'1/6','1/6'],[0,'-1/2','1/2'],['1/2']]:
            for lo,hi in [(-31,37),(-7,-2),(0,0),(5,12)]:
                p=analyze(cs,interval=[lo,hi]);F,L=p['numerator'],p['denominator']
                self.assertEqual(p['integral_input_count'],sum(ev(F,x)%L==0 for x in range(lo,hi+1)))
    def test_huge_interval_count(self):
        H=10**100;p=analyze(['1/2',0,'1/2'],interval=[-H,H])
        self.assertEqual(p['integral_input_count'],H)
    def test_binomial_gamma_bridge(self):
        for d in [0,1,2,8,16,32,64]:
            p=gamma_packet({'kind':'binomial','width':d},period_limit=1)
            self.assertTrue(p['integral_everywhere'])
            self.assertEqual(p['integer_domain_fixed_divisor'],1)
            self.assertEqual(p['numerator_fixed_divisor'],p['denominator'])
            for n in range(d,d+4):
                self.assertEqual(ev(p['numerator'],n)//p['denominator'],math.comb(n,d))
    def test_gamma_natural_domain(self):
        p=gamma_packet({'kind':'gamma_shift','a':2,'b':3,'shift':4},interval=[0,10])
        self.assertIn('natural',p['domain'])
        self.assertEqual(p['integral_input_count'],11)
        with self.assertRaises(ValueError):gamma_packet({'kind':'binomial','width':2},interval=[-1,3])
        for interval in [[],[0],3]:
            with self.assertRaises(ValueError):gamma_packet({'kind':'binomial','width':2},interval=interval)
    def test_input_rejection(self):
        for xs in [[],[True],[0.5],['nan'],['0.5'],['1/0'],['1e2'],'x']:
            with self.assertRaises(ValueError):analyze(xs)
        for k in [True,0,1025]:
            with self.assertRaises(ValueError):analyze([1],exponent=k)
        for interval in [[1,0],[True,3],[0]]:
            with self.assertRaises(ValueError):analyze([1],interval=interval)
    def test_budgets(self):
        with self.assertRaises(WorkLimit):analyze(['1/65537'])
        with self.assertRaises(WorkLimit):analyze([1]*130)
        with self.assertRaises(WorkLimit):analyze([1000003*1000033],factor_limit=1)
        with self.assertRaises(WorkLimit):native_certificate([1]*34)
        with self.assertRaises(WorkLimit):native_certificate(['1/4097'])
    def test_full_integrality_skips_residues(self):
        p=gamma_packet({'kind':'binomial','width':16},period_limit=1)
        self.assertGreater(p['denominator'],10**12)
        self.assertIsNone(p['integral_residues'])
    def test_native_source_binding(self):
        for cs in [[0,'-1/2','1/2'],['7/2',0,'1/2'],['1/2'],[0]]:
            p=native_certificate(cs);s=p['lean']['source']
            self.assertIn('rational_value_checked',s)
            self.assertFalse(p['lean']['kernel_checked'])
            self.assertEqual(hashlib.sha256(s.encode()).hexdigest(),p['lean']['source_sha256'])
            for forbidden in ['sorry','native_decide','Lean.ofReduceBool']:self.assertNotIn(forbidden,s)
    def test_service(self):
        for op in ['integer_valued_polynomial','native_integer_valued_certificate']:
            self.assertEqual(dispatch(None,{'op':op,'args':{'coefficients':[0,'-1/2','1/2']}})['integer_domain_fixed_divisor'],1)
        self.assertEqual(dispatch(None,{'op':'gamma_integer_arithmetic','args':{'spec':{'kind':'binomial','width':8}}})['integer_domain_fixed_divisor'],1)
    def test_independent_domain_and_gcd_census(self):
        rng=random.Random(7109)
        for _ in range(100):
            L=rng.randint(1,12);cs=[str(Q(rng.randint(-8,8),L)) for _ in range(rng.randint(1,6))]
            p=analyze(cs);F,L=p['numerator'],p['denominator'];d=len(F)-1
            vals=[ev(F,x)//L for x in range((d+1)*L) if ev(F,x)%L==0]
            self.assertEqual(math.gcd(*vals) if vals else 0,p['integer_domain_fixed_divisor'])
            for x in range(-30,31):
                self.assertEqual(ev(F,x)%L==0,p['integral_everywhere'] or x%L in p['integral_residues'])
    def test_quotient_period_requires_denominator(self):
        F,L,_=normalize([0,'-1/2','1/2']);q=4
        self.assertNotEqual((ev(F,1)//L)%q,(ev(F,5)//L)%q)
        for x in range(-30,31):self.assertEqual((ev(F,x)//L)%q,(ev(F,x+L*q)//L)%q)
