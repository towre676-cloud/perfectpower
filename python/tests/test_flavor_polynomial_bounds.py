from copy import deepcopy
from fractions import Fraction as Q
import unittest
from perfectpower.flavor_polynomial_bounds import (
    positive_halfline, verify_positive_halfline, rational_lower_bound,
    verify_rational_bound, bubble_shape_bracket, rational_absolute_budget,
    verify_absolute_budget)
from perfectpower.flavor_decay import compact_bubble_polynomials, optimize_shape


class PolynomialFlavorBounds(unittest.TestCase):
    def test_positive_with_negative_coefficients(self):
        self.assertTrue(verify_positive_halfline(positive_halfline([2,-2,1])))

    def test_constants(self):
        self.assertTrue(verify_positive_halfline(positive_halfline(['3/7'])))
        for f in ([0],[-1],[0,1]):
            with self.assertRaises(ValueError): positive_halfline(f)

    def test_reject_negative_well_and_even_zero_touch(self):
        for f in ([1,-3,1],[1,-2,1]):
            with self.assertRaises(ValueError): positive_halfline(f)

    def test_negative_repeated_root_allowed(self):
        self.assertTrue(verify_positive_halfline(positive_halfline([1,2,1])))

    def test_chain_tampering(self):
        c=positive_halfline([2,-2,1])
        for mutate in (lambda r:r['sturm_chain'].pop(),
                       lambda r:r['sturm_chain'][1].__setitem__(0,'999'),
                       lambda r:r.__setitem__('variations_at_zero_and_infinity',[0,0]),
                       lambda r:r.__setitem__('coefficients',['1','-3','1']),
                       lambda r:r.__setitem__('formal_verification',True)):
            bad=deepcopy(c);mutate(bad)
            self.assertFalse(verify_positive_halfline(bad))

    def test_sign_changing_denominator(self):
        # (x^2+1)/(x-1), x>1. Minimum=2+2sqrt(2)>4.
        c=rational_lower_bound([1,0,1],[-1,1],4,2)
        self.assertTrue(verify_rational_bound(c))
        self.assertEqual(Q(c['upper_bound']),5)
        with self.assertRaises(ValueError): rational_lower_bound([1,0,1],[-1,1],5,2)

    def test_reject_float_and_infeasible_witness(self):
        with self.assertRaises(ValueError): positive_halfline([1.0,1])
        for x in (-1,0,1):
            with self.assertRaises(ValueError): rational_lower_bound([1,0,1],[-1,1],4,x)

    def test_bound_identity_tampering(self):
        c=rational_lower_bound([1,0,1],[-1,1],4,2)
        for key,value in [('lower_bound','5'),('upper_bound','4'),('witness','4'),('denominator',['-2','1'])]:
            bad=deepcopy(c);bad[key]=value
            self.assertFalse(verify_rational_bound(bad))

    def test_bubble_entire_halfline(self):
        polynomials=compact_bubble_polynomials([0,0,1,-3,1],[[0,1]])
        proposed=optimize_shape(polynomials)
        cert=bubble_shape_bracket(polynomials,str(proposed['shape']))
        self.assertTrue(verify_rational_bound(cert))
        self.assertLess(Q(cert['lower_bound']),Q(cert['upper_bound']))

    def test_wrong_bubble_witness_rejected(self):
        with self.assertRaises(ValueError):
            bubble_shape_bracket({'kinetic_polynomial':[1], 'potential_polynomial':[1]},0)

    def test_uniform_response_budget(self):
        c=rational_absolute_budget([1],[2,1],1)
        self.assertTrue(verify_absolute_budget(c))
        bad=deepcopy(c);bad['budget']='1/4'
        self.assertFalse(verify_absolute_budget(bad))

    def test_budget_rejects_pole_and_threshold_violation(self):
        for N,D,b in (([1],[-1,1],10),([2],[1,1],1),([1],[1,1],0)):
            with self.assertRaises(ValueError): rational_absolute_budget(N,D,b)

    def test_existing_flavor_receipt_replay(self):
        import json
        from develop_flavor_polynomial_bounds import ROOT,verify_report
        report=json.loads((ROOT/'receipts/flavor_cosmology/polynomial_bounds.json').read_text())
        raw=(ROOT/'receipts/flavor_cosmology/tree_decay.json').read_bytes()
        self.assertTrue(verify_report(report,raw))
        self.assertFalse(verify_report(report,raw+b' '))
        bad=deepcopy(report);bad['mediator_lifts'][0]['mediator_mass']=6
        self.assertFalse(verify_report(bad,raw))
        bad=deepcopy(report);bad['source_candidates'][0]['certificate']['numerator'][0]='0'
        self.assertFalse(verify_report(bad,raw))


if __name__=='__main__': unittest.main()
