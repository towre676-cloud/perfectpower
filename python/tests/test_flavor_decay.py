import json
import unittest
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from scipy.integrate import quad
from perfectpower.flavor_decay import *

ROOT = Path(__file__).resolve().parents[2]


class ExactBubbleTests(unittest.TestCase):
    def setUp(self):
        # V(q)=q^2-3q^3+q^4: local false minimum, lower core.
        self.W = [0,0,1,-3,1]
        self.path = [[0,1],[2,3]]
        self.p = compact_bubble_polynomials(self.W,self.path)

    def test_interpolation_is_exact(self):
        p = [F(1,3),F(-7,11),F(5,13),F(19,17),F(-2,23)]
        self.assertEqual(interpolate([evaluate(p,F(j,4)) for j in range(5)]),p)

    def test_smooth_join(self):
        q = self.p["taper"]
        self.assertEqual(evaluate(q,0),1)
        self.assertEqual(evaluate(q,1),0)
        self.assertEqual(evaluate(derivative(q),0),0)
        self.assertEqual(evaluate(derivative(q),1),0)

    def test_independent_quadrature(self):
        L = 10
        q = lambda t:1-3*t*t+2*t**3
        dq = lambda t:-6*t+6*t*t
        T = quad(lambda t:(L+t)**3*10*dq(t)**2/2,0,1,epsabs=1e-10)[0]
        U = -L**4/4+quad(lambda t:(L+t)**3*float(evaluate(self.W,q(t))),0,1,epsabs=1e-10)[0]
        self.assertAlmostEqual(T,float(evaluate(self.p["kinetic_polynomial"],L)),places=9)
        self.assertAlmostEqual(U,float(evaluate(self.p["potential_polynomial"],L)),places=9)

    def test_scale_stationarity_and_negative_escape(self):
        b = bubble_at_shape(self.p,10)
        t,u = b["kinetic_integral"],b["potential_integral"]
        r2 = b["critical_scale_squared"]
        self.assertEqual(t+2*u*r2,0)
        self.assertGreater(t*r2+u*r2*r2,0)
        self.assertLess(t*4*r2+u*(4*r2)**2,0)

    def test_field_scale_cancels_action(self):
        scale_factor = F(7,3)
        scaled = compact_bubble_polynomials(scale(self.W,scale_factor**4),
                 [scale(p,scale_factor) for p in self.path])
        a,b = bubble_at_shape(self.p,10),bubble_at_shape(scaled,10)
        self.assertEqual(a["action_divided_by_pi_squared"],b["action_divided_by_pi_squared"])
        self.assertEqual(a["critical_scale_squared"]/scale_factor**2,b["critical_scale_squared"])

    def test_adding_canonical_fields_increases_fixed_shape_action(self):
        lifted = compact_bubble_polynomials(self.W,self.path+[[0,2,-1]])
        a,b = bubble_at_shape(self.p,10),bubble_at_shape(lifted,10)
        self.assertGreater(b["action_divided_by_pi_squared"],a["action_divided_by_pi_squared"])
        self.assertEqual(b["potential_integral"],a["potential_integral"])

    def test_invalid_exterior(self):
        with self.assertRaises(ValueError):
            compact_bubble_polynomials([1,-2],self.path)

    def test_no_lower_core(self):
        with self.assertRaises(ValueError):
            compact_bubble_polynomials([0,1],self.path)

    def test_constant_path(self):
        with self.assertRaises(ValueError):
            compact_bubble_polynomials(self.W,[[1]])

    def test_negative_shape(self):
        with self.assertRaises(ValueError):
            bubble_at_shape(self.p,-1)

    def test_shape_search_keeps_exact_witness(self):
        out = optimize_shape(self.p)
        replay = bubble_at_shape(self.p,out["shape"])
        self.assertEqual(out["action_divided_by_pi_squared"],replay["action_divided_by_pi_squared"])
        self.assertLessEqual(out["action_divided_by_pi_squared"],bubble_at_shape(self.p,10)["action_divided_by_pi_squared"])

    def test_nonfinite_coefficients(self):
        with self.assertRaises(ValueError):
            rat(float("nan"))


class PublishedActionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.r = json.loads((ROOT/"receipts/flavor_cosmology/tree_decay.json").read_text())

    def test_published_metastability_not_stable_wall_claim(self):
        v = self.r["published_vacuum_status"]
        self.assertGreater(v["energy_gap"],0.014)
        self.assertLess(v["false_gradient_norm"],1e-10)
        self.assertLess(v["lower_gradient_norm"],1e-10)
        self.assertFalse(v["global_winner_classified"])

    def test_full_action_polynomial_replay(self):
        self.assertTrue(all(c["potential_replay_maximum_error"]<2e-11 for c in self.r["candidates"]))
        self.assertTrue(all(c["endpoint_gradient_norm"]<2e-10 for c in self.r["candidates"]))

    def test_exact_retained_actions(self):
        for c in self.r["candidates"]:
            p = {k:list(map(F,v)) for k,v in c["radial_polynomials"].items()}
            out = bubble_at_shape(p,F(c["bubble"]["shape"]))
            self.assertEqual(str(out["action_divided_by_pi_squared"]),c["bubble"]["action_divided_by_pi_squared"])

    def test_mediator_matching_and_positive_cost(self):
        c = self.r["completion"]
        self.assertEqual(c["total_canonical_coordinates"],48)
        self.assertEqual(c["mediator_coordinates"],27)
        self.assertLess(c["current_replay_maximum_error"],1e-12)
        self.assertLess(c["positive_square_replay_maximum"],1e-20)
        self.assertTrue(all(F(v)>=0 for v in c["kinetic_increase_polynomial"]))
        self.assertGreater(F(c["fixed_shape_action_ratio"]),1)

    def test_decoupling_scan(self):
        rows = self.r["completion"]["mass_scan"]
        ratios = [r["ratio_to_source_candidate"] for r in rows]
        self.assertTrue(all(a>b>1 for a,b in zip(ratios,ratios[1:])))
        self.assertLess(ratios[-1]-1,ratios[0]-1)

    def test_CP_pair_does_not_get_a_bias(self):
        self.assertLess(abs(self.r["CP_pair"]["energy_difference"]),1e-11)
        self.assertLess(self.r["CP_pair"]["sample_full_potential_CP_error"],1e-11)


if __name__ == "__main__":
    unittest.main()
