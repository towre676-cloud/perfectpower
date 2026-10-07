from math import sqrt, pi
import unittest
import numpy as np
from perfectpower import wall_nucleation as wn


class Bounces(unittest.TestCase):
    def test_virial_and_thin_wall_limit(self):
        for d in (3, 4):
            b = wn.bounce(.02, d)
            self.assertLess(abs(b['virial_defect']), 1e-6)
            self.assertLess(abs(b['s']/wn.thin_wall(.02, d) - 1), 4e-3)
            b = wn.bounce(.3, d)
            self.assertLess(abs(b['virial_defect']), 1e-8)

    def test_spinodal_law_against_cubic_reduction(self):
        for d, C in ((3, 62.148), (4, 179.36)):
            self.assertAlmostEqual(wn.spinodal_constant_exact(d), C, delta=.02)
            x = 1e-5
            r = wn.bounce(wn.EPS_SPINODAL - x, d)['s']/x**((6 - d)/4)
            self.assertLess(abs(r/wn.spinodal_constant_exact(d) - 1), 2e-2)

    def test_actions_decrease_with_bias_and_guards(self):
        s = [wn.bounce(e, 4)['s'] for e in (.1, .2, .3)]
        self.assertTrue(s[0] > s[1] > s[2])
        with self.assertRaises(ValueError):
            wn.reduced_vacua(.4)
        with self.assertRaises(ValueError):
            wn.bounce(.1, 2)

    def test_critical_eps_inverts_action(self):
        e, how = wn.critical_eps(100., 4)
        self.assertEqual(how, 'bounce')
        self.assertAlmostEqual(wn.bounce(e, 4)['s'], 100., places=5)
        e2, how2 = wn.critical_eps(1e-5, 3)
        self.assertEqual(how2, 'near_spinodal_asymptotic')
        self.assertLess(wn.EPS_SPINODAL - e2, 1e-8)


class Transition(unittest.TestCase):
    def test_loop_parameter_is_coupling_independent(self):
        g = [wn.perturbative_transition(l, 30000., l/4)['loop_parameter'] for l in (.02, .2)]
        self.assertAlmostEqual(g[0], g[1], places=10)
        self.assertGreater(g[0], .05)

    def test_degenerate_minima_at_Tc(self):
        r = wn.perturbative_transition(.1, 30000., .025)
        T, p = r['Tc'], r['phic_over_Tc']*r['Tc']
        dv = wn.resummed_potential(p, T, .1, 30000., .025) - wn.resummed_potential(0., T, .1, 30000., .025)
        self.assertLess(abs(dv), 1e-6*abs(wn.resummed_potential(p/2, T, .1, 30000., .025)))
        self.assertGreater(T, r['T0'])

    def test_lifting_ratio_and_threshold(self):
        b = wn.bounce(.37, 4)
        d = wn.lifting_ratio(b['profile_r'], b['profile_phi'], 4, .1, 10., 1e-7/.13, 246/30000, 1.)
        self.assertGreater(d, 0); self.assertLess(d, 4e-6)
        s, S = wn.nucleation_threshold(4, 10., 1e-25)
        self.assertAlmostEqual(S, 4*np.log(1e25) + 2*np.log(S/(2*pi)), places=8)


if __name__ == '__main__':
    unittest.main()
