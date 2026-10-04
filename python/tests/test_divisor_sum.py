import itertools
import json
import tempfile
import unittest
from math import isqrt
from perfectpower.divisor_sum import (geometric_sum,sigma_sieve,exact_root,
    square_product_witness,prime_power_rows,prime_pair_squares,square_classes)


class DivisorSumTests(unittest.TestCase):
    def test_sieve_independent_divisor_enumeration(self):
        sigma,primes=sigma_sieve(1500)
        for n in range(1,1501):
            self.assertEqual(sigma[n],sum(d for d in range(1,n+1) if n%d==0))
        self.assertEqual(primes,[p for p in range(2,1501)
                                if all(p%d for d in range(2,isqrt(p)+1))])

    def test_geometric_sum_and_prime_power_formula(self):
        sigma,_=sigma_sieve(10000)
        for p in (2,3,5,7,11):
            for a in range(7):
                self.assertEqual(geometric_sum(p,a),sum(p**i for i in range(a+1)))
                if p**a<=10000:self.assertEqual(geometric_sum(p,a),sigma[p**a])
        self.assertEqual(geometric_sum(1,100),101)
        self.assertEqual(geometric_sum(0,10),1)

    def test_integer_roots_exact_and_adjacent(self):
        for d in range(2,9):
            for r in range(2,150):
                self.assertEqual(exact_root(r**d,d),r)
                self.assertIsNone(exact_root(r**d-1,d))
                self.assertIsNone(exact_root(r**d+1,d))
        self.assertEqual(exact_root(10**1000,5),10**200)
        self.assertEqual(exact_root(0,3),0)
        self.assertEqual(exact_root(1,8),1)

    def test_square_join_exhaustive(self):
        for a,b in itertools.product(range(1,180),repeat=2):
            result=square_product_witness(a,b)
            self.assertEqual(result is not None,isqrt(a*b)**2==a*b)
            if result:self.assertEqual(result['product_root']**2,a*b)

    def test_prime_pair_grid_independent_brute_force(self):
        rows=prime_power_rows(47,5)
        groups,hits=prime_pair_squares(rows)
        actual={(r['p'],r['a'],r['q'],r['b']) for r in hits}
        expected={(l['prime'],l['exponent'],r['prime'],r['exponent'])
                  for l,r in itertools.product(rows,repeat=2)
                  if l['prime']<r['prime'] and
                  isqrt(l['sigma']*r['sigma'])**2==l['sigma']*r['sigma']}
        self.assertEqual(actual,expected)
        self.assertEqual(len(actual),len(hits))
        self.assertEqual(sorted(i for g in groups for i in g),list(range(len(rows))))
        self.assertTrue(any(not r['both_factors_square'] for r in hits))
        for r in hits:self.assertEqual(r['root']**2,r['sigma'])

    def test_nonsquare_factors_can_make_square(self):
        # sigma(2)=3, sigma(11)=12, sigma(22)=36.
        result=square_product_witness(3,12)
        self.assertEqual(result,{'gcd':3,'left_root':1,'right_root':2,'product_root':6})
        self.assertIsNone(square_product_witness(3,4))

    def test_factorization_validation_and_repunit(self):
        from perfectpower.divisor_sum import sigma_from_factorization,repunit_quartic
        self.assertEqual(sigma_from_factorization([[2,1],[11,1]])['sigma'],36)
        self.assertEqual(sigma_from_factorization([])['sigma'],1)
        for factors in ([[4,1]],[[2,1],[2,2]],[[3,0]],[[True,2]]):
            with self.assertRaises(ValueError):sigma_from_factorization(factors)
        self.assertEqual(repunit_quartic()['prime_inputs'],[3])
        for shift in (-5,0,5):
            result=repunit_quartic(shift)
            for p in result['prime_inputs']:
                self.assertTrue(any(x==p for x,y in result['points']))

    def test_reject_invalid_domains(self):
        for args in ((True,1),(-1,1),(2,-1)):
            with self.assertRaises(ValueError):geometric_sum(*args)
        for args in ((-1,2),(4,1),(4,True)):
            with self.assertRaises(ValueError):exact_root(*args)
        with self.assertRaises(ValueError):sigma_sieve(-1)
        with self.assertRaises(ValueError):square_product_witness(0,1)
        self.assertEqual(sigma_sieve(0),([0],[]))

    def test_catalogue_replay_and_scope(self):
        from pathlib import Path
        path=Path(__file__).resolve().parents[2]/'receipts/divisor_sum'
        if not (path/'complete_quartics.json').exists():self.skipTest('generate catalogue first')
        packet=json.loads((path/'complete_quartics.json').read_text())
        seen=set()
        for row in packet['rows']:
            f=row['coefficients']; key=tuple(f)
            self.assertNotIn(key,seen);seen.add(key)
            self.assertTrue(row['complete']);self.assertFalse(row['execution_verified'])
            self.assertEqual(len(row['points']),len({tuple(p) for p in row['points']}))
            for x,y in row['points']:
                self.assertLessEqual(abs(x),row['coordinate_bound'])
                self.assertEqual(y*y,sum(c*x**i for i,c in enumerate(f)))
        repunit=next(r for r in packet['rows'] if r['coefficients']==[1,1,1,1,1])
        self.assertEqual(repunit['points'],[[-1,-1],[-1,1],[0,-1],[0,1],[3,-11],[3,11]])
        bounded=json.loads((path/'bounded_power_hits.json').read_text())
        self.assertFalse(bounded['globally_complete'])
        for degree,hits in bounded['hits'].items():
            for n,s,r in hits:self.assertEqual(r**int(degree),s)

if __name__=='__main__':unittest.main()
