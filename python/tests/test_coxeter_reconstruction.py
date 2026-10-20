import json
import math
import unittest
from fractions import Fraction as Q

from perfectpower.coxeter_reconstruction import (
    annihilator_from_moments, folded_profile, odd_mellin_coefficients,
    positive_certificate, power_from_raghava, power_moments, predict_moments,
    receipt, recover_orientation, sharpness_witness, symmetric_profile)
from perfectpower.period_transport import PhaseObject
from perfectpower.raghava_coxeter import e8_reflection_spectrum, e8_adjoint_spectrum, moment_vector


class CoxeterReconstructionTests(unittest.TestCase):
    def test_e8_nine_coordinate_certificate(self):
        p = e8_reflection_spectrum()
        nodes = tuple(Q(i, 225) for i in (1, 4, 16, 49))
        cert = positive_certificate(power_moments(p, 8), nodes)
        self.assertEqual(cert['weights'], (2, 2, 2, 2))
        self.assertEqual(cert['square_integral'], 0)
        self.assertEqual(cert['sufficient_coordinates'], 9)
        self.assertEqual(cert['annihilator'], tuple(map(Q, ('3136/2562890625', '-836/2278125', '371/16875', '-14/45', '1'))))

    def test_hankel_determinant_matches_independent_vandermonde(self):
        p = e8_reflection_spectrum()
        profile = folded_profile(p)
        nodes, weights = zip(*profile)
        cert = positive_certificate(power_moments(p, 8), nodes)
        determinant = math.prod(weights)
        for i in range(4):
            for j in range(i+1, 4):
                determinant *= (nodes[j]-nodes[i])**2
        self.assertEqual(cert['hankel_determinant'], determinant)

    def test_recurrence_predicts_all_later_moments(self):
        p = e8_reflection_spectrum()
        direct = power_moments(p, 32)
        annihilator = annihilator_from_moments(direct[:8], 4)
        self.assertEqual(predict_moments(direct[:4], annihilator, 32), direct)

    def test_exact_raghava_normalization(self):
        for n in range(1, 13):
            p = PhaseObject(n, tuple((j, j+1) for j in range(n)))
            self.assertEqual(power_from_raghava(moment_vector(p, 8)), power_moments(p, 8))

    def test_positive_profiles_through_conductor_twelve(self):
        for n in range(1, 13):
            p = PhaseObject(n, tuple((j, Q(j+1, n+1)) for j in range(n)))
            profile = folded_profile(p)
            cert = positive_certificate(power_moments(p, 2*len(profile)), [x for x, _ in profile])
            self.assertEqual(tuple(zip(cert['nodes'], cert['weights'])), profile)

    def test_positive_sharpness_witness(self):
        r = sharpness_witness()
        self.assertEqual(r['epsilon'], Q(14144, 3243658447265625))
        self.assertEqual(r['profile'].conductor, 30)
        self.assertTrue(all(w > 0 for w in r['weights']))
        expected, actual = power_moments(e8_reflection_spectrum(), 8), power_moments(r['profile'], 8)
        self.assertEqual(expected[:8], actual[:8])
        self.assertNotEqual(expected[8], actual[8])
        self.assertFalse(r['integer_dimension_eight_minimality_claimed'])

    def test_even_coordinates_lose_orientation(self):
        p = PhaseObject(7, ((1, 3), (2, 1)))
        self.assertNotEqual(p, p.dual())
        self.assertEqual(power_moments(p, 16), power_moments(p.dual(), 16))
        self.assertNotEqual(odd_mellin_coefficients(p, 2), odd_mellin_coefficients(p.dual(), 2))

    def test_orientation_through_conductor_fourteen_with_endpoints(self):
        for n in range(1, 15):
            p = PhaseObject(n, tuple((j, j+1) for j in range(n)))
            profile = folded_profile(p)
            nodes, weights = zip(*profile)
            count = sum(0 < x < Q(1, 4) for x in nodes)
            recovered = recover_orientation(nodes, weights, odd_mellin_coefficients(p, count))
            self.assertEqual(recovered.lift(n), p)

    def test_odd_mellin_matches_independent_absolutely_convergent_sine_series(self):
        p = PhaseObject(7, ((1, 3),))
        coefficient = odd_mellin_coefficients(p, 1)[0]
        n = 5000
        partial = sum(3*math.sin(2*math.pi*j/7)/j**3 for j in range(1, n+1))
        self.assertLessEqual(abs(partial-float(coefficient)*math.pi**3), 3/(2*n*n)+1e-13)

    def test_rejects_missing_moment_wrong_node_and_negative_weights(self):
        moments = power_moments(e8_reflection_spectrum(), 8)
        nodes = [Q(i, 225) for i in (1, 4, 16, 49)]
        for m, n in ((moments[:-1], nodes), (moments, nodes[:-1]+[Q(1, 4)])):
            with self.assertRaises(ValueError):
                positive_certificate(m, n)
        with self.assertRaises(ValueError):
            folded_profile(PhaseObject(7, ((1, -1),)))
        with self.assertRaises(ValueError):
            positive_certificate((1.0, 2, 3), [0])
        with self.assertRaises(ValueError):
            recover_orientation([Q(1, 16)], [2], [100])

    def test_signed_competitor_exhibits_positivity_boundary(self):
        nodes = tuple(Q(j, 40) for j in range(10))
        delta = [1/math.prod(x-y for j, y in enumerate(nodes) if i != j) for i, x in enumerate(nodes)]
        # This rational-node identity holds regardless of square-root extraction.
        self.assertTrue(any(d < 0 for d in delta))
        self.assertEqual([sum(d*x**k for d, x in zip(delta, nodes)) for k in range(9)], [0]*9)

    def test_receipt_serializes_and_retains_scope(self):
        result = receipt()
        json.dumps(result, allow_nan=False)
        self.assertEqual(result['reflection']['sufficient_coordinates'], 9)
        self.assertEqual(result['reflection']['odd_coordinates'], 4)
        self.assertEqual(result['adjoint']['sufficient_coordinates'], 33)
        self.assertEqual(result['adjoint']['odd_coordinates'], 14)
        self.assertFalse(result['formal_kernel_verified'])


if __name__ == '__main__':
    unittest.main()
