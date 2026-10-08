from pathlib import Path
from fractions import Fraction
import unittest,json,copy
try:
    from flint import arb,arb_poly,ctx
    import sympy
except ImportError as exc:
    raise unittest.SkipTest('Install python/requirements-wall-intervals.txt for the interval research tests') from exc
from perfectpower.wall_profile_intervals import bernstein_range,quintic,ball,check_seed,exact_profile_identities

root=Path(__file__).resolve().parents[2]

class ProfileIntervalAlgebra(unittest.TestCase):
    def test_full_potential_identities_and_odd_gap(self):
        identities=exact_profile_identities()
        self.assertEqual(len(identities),10);self.assertTrue(all(v=='0' for v in identities.values()))

    def test_Bernstein_encloses_hidden_extremum(self):
        p=arb_poly([0,4,-4]);lo,hi=bernstein_range(p)
        self.assertLessEqual(lo,0);self.assertGreaterEqual(hi,1)
        self.assertGreaterEqual(hi,p(ball(Fraction(1,2))))

    def test_quintic_matches_both_values_slopes_and_curvatures(self):
        old=ctx.prec;ctx.prec=160
        try:
            p=quintic((arb(2),arb(3)),(arb(5),arb(7)),arb(11),arb(13),arb(2))
            self.assertTrue(p(0).contains(2));self.assertTrue(p(1).contains(5))
            self.assertTrue((p.derivative()(0)/2).contains(3));self.assertTrue((p.derivative()(1)/2).contains(7))
            self.assertTrue((p.derivative().derivative()(0)/4).contains(11));self.assertTrue((p.derivative().derivative()(1)/4).contains(13))
        finally:ctx.prec=old

    def test_bad_seed_or_precision_rejected(self):
        with self.assertRaises(ValueError):check_seed({})
        with self.assertRaises(ValueError):check_seed({'format':'pp-wall-dyadic-seed/1'},precision=32)

class WholeLineCertificate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.seed=json.loads((root/'receipts/flavor_cosmology/wall_profile_interval_seed.json').read_text())
        cls.report=check_seed(cls.seed)

    def test_continuous_existence_and_all_signs(self):
        r=self.report
        self.assertTrue(r['continuous_whole_line_wall_existence_certified'])
        self.assertTrue(r['whole_line_asymptotic_vacuum_certified'])
        self.assertTrue(all(v for k,v in r.items() if k.startswith('P')))
        self.assertTrue(r['Higgs_at_least_vacuum_everywhere'])
        self.assertLess(r['bounds_display_float']['uniform_solution_error_upper'],1e-6)
        self.assertGreater(r['bounds_display_float']['Higgs_profile_lower'],.008)

    def test_independent_higher_precision_replay(self):
        higher=check_seed(self.seed,precision=192)
        for key in ['source_floor','Higgs_floor_retained','existence_boundary_ratio','uniform_solution_error_upper']:
            self.assertAlmostEqual(higher['bounds_display_float'][key],self.report['bounds_display_float'][key],places=12)

    def test_too_small_existence_ball_rejected(self):
        with self.assertRaises(ArithmeticError):check_seed(self.seed,radius_ball='0.00000001')

    def test_nonpositive_parameters_rejected(self):
        bad=copy.deepcopy(self.seed);bad['parameters']['kappa']='-0.0000001'
        with self.assertRaises(ValueError):check_seed(bad)

    def test_deliberately_damaged_profile_rejected(self):
        bad=copy.deepcopy(self.seed);bad['values_hex'][512][0]=float(.01).hex()
        with self.assertRaises(ArithmeticError):check_seed(bad)

if __name__=='__main__':unittest.main()
