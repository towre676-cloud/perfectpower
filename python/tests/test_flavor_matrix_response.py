from copy import deepcopy
from fractions import Fraction as Q
from itertools import permutations
import json
import random
import unittest
from perfectpower import polyalg as P
from perfectpower.flavor_matrix_response import (
    constants,determinant,positive_interval,verify_interval,
    positive_definite,verify_positive_definite,relaxed_response,verify_response,
    protected_response,verify_protected_response,
    operator_norm_envelope,verify_norm_envelope,
    rectangular_norm_envelope,verify_rectangular_envelope)


def permutation_determinant(A):
    total=P.ZERO
    for perm in permutations(range(len(A))):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(len(A)) for j in range(i+1,len(A)))
        product=P.ONE
        for i,j in enumerate(perm):product=P.mul(product,P.poly(A[i][j]))
        total=P.add(total,P.scale(product,sign))
    return total


class MatrixFlavorResponses(unittest.TestCase):
    def test_bareiss_against_independent_permutation_expansion(self):
        rng=random.Random(1181)
        for n in range(1,5):
            for _ in range(4):
                A=[[[Q(rng.randrange(-3,4)),Q(rng.randrange(-2,3))] for j in range(n)] for i in range(n)]
                self.assertEqual(determinant(A),permutation_determinant(A))

    def test_row_pivot_and_identically_singular_matrix(self):
        self.assertEqual(determinant([[[0],[0,1]],[[1],[2]]]),P.poly([0,-1]))
        self.assertEqual(determinant([[[1],[2]],[[2],[4]]]),P.ZERO)

    def test_finite_interval_both_endpoints(self):
        c=positive_interval([1,0,-1],'0','1/2')
        self.assertTrue(verify_interval(c))
        self.assertEqual(Q(c['right_endpoint_value']),Q(3,4))
        for lo,hi in ((0,1),(1,0),(-2,0)):
            with self.assertRaises(ValueError): positive_interval([1,0,-1],lo,hi)

    def test_interval_interior_zero_detected(self):
        with self.assertRaises(ValueError):positive_interval(['1/4',-1,1],0,1)

    def test_interval_tampering(self):
        c=positive_interval([1,0,-1],0,'1/2')
        for key,v in [('interval',['0','2']),('right_endpoint_value','1')]:
            bad=deepcopy(c);bad[key]=v;self.assertFalse(verify_interval(bad))

    def test_continuous_matrix_stability(self):
        H=[[[2,1],[1]],[[1],[3,1]]]
        self.assertTrue(verify_positive_definite(positive_definite(H)))
        self.assertTrue(verify_positive_definite(positive_definite(H,interval=('0/1','2/1'))))

    def test_indefinite_asymmetric_and_gauge_null_rejected(self):
        for H in ([[[1],[2]],[[2],[1]]],[[[1],[1]],[[0],[1]]],[[[1],[0]],[[0],[0]]]):
            with self.assertRaises(ValueError):positive_definite(H)

    def test_matrix_stability_tampering(self):
        c=positive_definite([[[2,1],[1]],[[1],[3,1]]])
        bad=deepcopy(c);bad['principal_minors'][1][0]='99'
        self.assertFalse(verify_positive_definite(bad))
        bad=deepcopy(c);bad['matrix'][0][1]=['2']
        self.assertFalse(verify_positive_definite(bad))

    def test_bordered_response_against_two_by_two_inverse(self):
        H=[[[2,1],[1]],[[1],[3,1]]];g=[[2],[0,1]];o=[[1],[3]];direct=[-1,1]
        r=relaxed_response(H,g,o,direct)
        self.assertTrue(verify_response(r))
        for t in (Q(0),Q(1,3),Q(2),Q(7)):
            # independent explicit inverse of [[t+2,1],[1,t+3]]
            determinant_value=(t+2)*(t+3)-1
            inverse_pairing=(2*((t+3)-3)+t*(-1+3*(t+2)))/determinant_value
            expected=t-1-inverse_pairing
            self.assertEqual(P.evaluate(P.poly(map(Q,r['numerator'])),t)/P.evaluate(P.poly(map(Q,r['denominator'])),t),expected)

    def test_cancelled_response_keeps_physical_singularity(self):
        H=[[[1],[0,1]],[[0,1],[1]]]
        r=relaxed_response(H,[[1],[0,1]],[[1],[0]],direct=[1])
        self.assertEqual(r['numerator'],['0']);self.assertEqual(r['denominator'],['1','0','-1'])
        with self.assertRaises(ValueError):protected_response(H,[[1],[0,1]],[[1],[0]],1,direct=[1])

    def test_stable_response_interval_and_budget_rejection(self):
        H=[[[1],[0,1]],[[0,1],[1]]]
        c=protected_response(H,[[1],[0]],[[1],[0]],'27/20',interval=(0,'1/2'))
        self.assertTrue(verify_protected_response(c))
        with self.assertRaises(ValueError):protected_response(H,[[1],[0]],[[1],[0]],1,interval=(0,'1/2'))
        bad=deepcopy(c);bad['budget']='1';self.assertFalse(verify_protected_response(bad))

    def test_symmetric_norm_bound(self):
        E=constants([[0,'1/3'],['1/3',0]])
        self.assertTrue(verify_norm_envelope(operator_norm_envelope(E,'1/2')))
        with self.assertRaises(ValueError):operator_norm_envelope(E,'1/4')

    def test_rectangular_norm_and_tampering(self):
        B=[[[Q(3,5)]],[[Q(4,5)]]]
        c=rectangular_norm_envelope(B,'11/10');self.assertTrue(verify_rectangular_envelope(c))
        with self.assertRaises(ValueError):rectangular_norm_envelope(B,1)
        bad=deepcopy(c);bad['block'][0][0]=['1'];self.assertFalse(verify_rectangular_envelope(bad))

    def test_exact_input_and_dimension_validation(self):
        for A in ([[[1.0]]],[],[[[1],[2]]]):
            with self.assertRaises(ValueError):determinant(A)
        with self.assertRaises(ValueError):relaxed_response(constants([[1]]),[[1],[0]],[[1]])
        with self.assertRaises(ValueError):relaxed_response(constants([[0]]),[[1]],[[1]])

    def test_published_21_field_envelopes_and_source_link(self):
        from develop_flavor_matrix_response import ROOT,verify_report
        raw=(ROOT/'receipts/m22_interactions/flavor_spectral_matching.json').read_bytes()
        r=json.loads((ROOT/'receipts/flavor_cosmology/matrix_response.json').read_text())
        self.assertTrue(verify_report(r,raw))
        self.assertFalse(verify_report(r,raw+b' '))
        bad=deepcopy(r);bad['metric_envelopes']['finite27']['metric_error_certificate']['matrix'][0][0]=['1']
        self.assertFalse(verify_report(bad,raw))


if __name__=='__main__':unittest.main()
