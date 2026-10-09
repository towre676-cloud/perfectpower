import copy
import os
import random
import unittest
from perfectpower.checked_box import box_certificate,check_box
from perfectpower.divisor_square import WorkLimit


class CheckedBoxTests(unittest.TestCase):
    def test_original_signed_equation_and_tied_minimum(self):
        p=box_certificate([-2,0,0,1],2,[-2,5],ranks=[0,1],objective=[0,1])
        self.assertEqual(p['points'],[[3,-5],[3,5]])
        self.assertEqual(p['minimum'],{'value':3,'points':[[3,-5],[3,5]]})
        self.assertIn('all integer y',p['scope'])
        self.assertIn('complete_all_integer_y',p['lean'])

    def test_random_original_equations_against_independent_scan(self):
        rng=random.Random(25)
        for _ in range(40):
            cs=[rng.randint(-3,3) for _ in range(4)];d=rng.randint(2,5)
            p=box_certificate(cs,d,[-3,3])
            expected=[[x,y] for x in range(-3,4) for y in range(-100,101)
                      if y**d==sum(c*x**i for i,c in enumerate(cs))]
            self.assertEqual(p['points'],expected)

    def test_empty_negative_odd_and_zero(self):
        self.assertEqual(box_certificate([0,1],3,[-2,2])['points'],[[-1,-1],[0,0],[1,1]])
        self.assertEqual(box_certificate([0],2,[-2,2])['points'],[[x,0] for x in range(-2,3)])
        self.assertEqual(box_certificate([-1],2,[-2,2])['count'],0)
        self.assertEqual(box_certificate([1],2,[2,1])['count'],0)

    def test_explicit_rectangle_preserved(self):
        p=box_certificate([-2,0,0,1],2,[-2,5],[0,6])
        self.assertEqual(p['points'],[[3,5]])
        self.assertNotIn('complete_all_integer_y',p['lean'])

    def test_mutations_rejected_before_toolchain_execution(self):
        p=box_certificate([0,1],2,[0,4])
        for key,value in [('points',[]),('count',999),('lean','axiom falseProof : False'),
                          ('source_sha256','0'*64),('proof_status','kernel_checked')]:
            altered=copy.deepcopy(p);altered[key]=value
            self.assertFalse(check_box(altered,lean='does-not-exist')['accepted'])

    def test_input_and_work_budgets(self):
        for cs,d,x,y in [([True],2,[0,1],None),([1],True,[0,1],None),
                         ([1],2,[0.5,1],None),([1],2,[0,1],[False,2])]:
            with self.assertRaises(ValueError):box_certificate(cs,d,x,y)
        with self.assertRaises(WorkLimit):box_certificate([1],2,[0,100000])
        with self.assertRaises(WorkLimit):box_certificate([1],2,[0,1],[-10000,10000])

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_LEAN'),'explicit Lean toolchain required')
    def test_actual_kernel_acceptance_of_original_sources(self):
        cases=[([-2,0,0,1],2,[-2,5],None),([0,1],3,[-3,3],None),
               ([-1],2,[-2,2],None),([0],2,[-2,2],None),
               ([1],2,[2,1],None),([0,0,0,0,1],2,[-2,2],None),
               ([-2,0,0,1],2,[-2,5],[0,6])]
        for cs,d,x,y in cases:
            p=box_certificate(cs,d,x,y,objective=[0,1])
            receipt=check_box(p)
            self.assertTrue(receipt['accepted'],receipt)
            self.assertFalse(receipt['execution_verified'])


if __name__=='__main__':unittest.main()
