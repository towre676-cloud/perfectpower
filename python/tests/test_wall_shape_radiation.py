from dataclasses import replace
from math import sqrt, pi
import unittest
import numpy as np
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall, solve_coupled_wall, potential_and_hessian
from perfectpower import wall_scattering as ws
from perfectpower import wall_shape_radiation as sr

MODEL = WallModel(30000., .1, .025000033333333335, 300000., 3000.)


class CubicVertex(unittest.TestCase):
    def test_vertex_is_derivative_of_published_hessian(self):
        bath = HiggsWall(portal=.01)
        wall = solve_coupled_wall(MODEL, HiggsWall())
        wall['bath'] = bath
        z = np.array([.3, -.002, .01]); e = 1e-6
        fd = np.array([(potential_and_hessian(MODEL, bath, *(z + e*np.eye(3)[i]))[1]
                        - potential_and_hessian(MODEL, bath, *(z - e*np.eye(3)[i]))[1])/(2*e) for i in range(3)])
        saved = sr._profile
        try:
            sr._profile = lambda w, rho: z[:, None]*np.ones((1, np.size(rho)))
            T = sr.cubic_vertex(wall, [0.])[0]
        finally:
            sr._profile = saved
        np.testing.assert_allclose(T, fd, atol=1e-9)
        np.testing.assert_allclose(T, T.transpose(1, 0, 2)); np.testing.assert_allclose(T, T.transpose(2, 1, 0))


class SecondHarmonic(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.wall = solve_coupled_wall(MODEL, HiggsWall())
        cls.state = ws.shape_bound_state(cls.wall)
        cls.r = sr.second_harmonic(cls.wall, cls.state)

    def test_closed_form_integral_and_pure_kink(self):
        cf = sr.kink_closed_form(.1)
        self.assertAlmostEqual(cf['Gamma_NL_over_A2'], 2*cf['P1']/(3*.05), places=15)
        pt = solve_coupled_wall(replace(MODEL, current_g_GeV=0.), HiggsWall(portal=0.))
        r = sr.second_harmonic(pt, ws.shape_bound_state(pt))
        self.assertLess(abs(r['P1']/cf['P1'] - 1), 1e-8)
        self.assertEqual(r['channel_power'][0], 0.)

    def test_physical_power_converged_and_in_source_channel(self):
        self.assertEqual(self.r['open_channels'], [0, 1])
        self.assertLess(self.r['channel_power'][0], 1e-15*self.r['P1'])
        self.assertAlmostEqual(self.r['Omega2']/self.state['E'], 4)
        r2 = sr.second_harmonic(self.wall, self.state, R=200.)
        self.assertLess(abs(r2['P1']/self.r['P1'] - 1), 1e-9)
        self.assertLess(abs(self.r['P1']/sr.kink_closed_form(.1)['P1'] - 1), 1e-4)

    def test_crossover_equates_rates(self):
        G = 7.9e-18
        c = sr.crossover(self.r['P1'], self.state['E'], G)
        self.assertAlmostEqual(self.r['Gamma_NL_over_A2']*c['A_c']**2/c['linear_rate'], 1, places=12)
        self.assertGreater(c['A_c'], 1e-8); self.assertLess(c['A_c'], 1e-6)


class TimeDomain(unittest.TestCase):
    def test_nonlinear_simulation_matches_closed_form(self):
        t, a = sr.kink_time_domain(.1, .2, dx=.1, half_width=400., t_end=700., samples=20000)
        env = sr.envelope(t, a, 2*pi/sqrt(.15))
        m = env[:, 0] > 200
        slope = np.polyfit(env[m, 0], 1/env[m, 1]**2, 1)[0]
        self.assertLess(abs(slope/sr.kink_closed_form(.1)['Gamma_NL_over_A2'] - 1), .03)


if __name__ == '__main__':
    unittest.main()
