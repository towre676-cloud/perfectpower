from dataclasses import replace
import unittest
import numpy as np
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall, solve_coupled_wall
from perfectpower import wall_continuum_stability as cs

MODEL = WallModel(30000., .1, .025000033333333335, 300000., 3000.)


class ContinuumStability(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.wall = solve_coupled_wall(MODEL, HiggsWall())

    def test_hypotheses_hold_on_core_and_tail(self):
        self.assertTrue(cs.sign_certificate(self.wall)['all_strict'])
        t = cs.tail_certificate(self.wall)
        self.assertTrue(t['all_hold'])
        self.assertLess(abs(t['decaying_mode_consistency'][0]), 1e-3)

    def test_cooperative_identity_matches_quadratic_form(self):
        f = (lambda r: np.cos(.3*r) + .2, lambda r: np.exp(-r/5)*(1 + r), lambda r: np.sin(.1*r)**2 + .5)
        r = cs.translation_identity(self.wall, f)
        self.assertGreater(r['rhs'], 0)
        self.assertLess(abs(r['lhs'] - r['rhs'])/r['rhs'], 1e-6)
        # psi proportional to the zero mode gives zero.
        one = (lambda r: 1 + 0*r,)*3
        z = cs.translation_identity(self.wall, one)
        self.assertLess(abs(z['lhs']), 1e-10)

    def test_opposite_supersolution_and_goldstones(self):
        o = cs.opposite_supersolution(self.wall)
        self.assertLess(o['max_relative_residual'], 1e-7)
        self.assertGreater(o['margin'], .19)
        g = cs.goldstone_factorization(self.wall)
        self.assertLess(g['max_abs_difference'], 1e-18)
        self.assertGreaterEqual(cs.maximum_principle_lemma(self.wall)['min_h_minus_h0'], 0.)

    def test_decoupled_mediator_case(self):
        w = solve_coupled_wall(replace(MODEL, current_g_GeV=0.), HiggsWall())
        c = cs.sign_certificate(w)
        self.assertTrue(c['mediator_decoupled'] and c['all_strict'])
        self.assertNotIn('dy_negative', cs.tail_certificate(w)['rows'])


if __name__ == '__main__':
    unittest.main()
