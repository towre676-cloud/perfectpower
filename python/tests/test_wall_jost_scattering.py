from dataclasses import replace
from math import sqrt
import unittest
import numpy as np
from scipy.integrate import solve_ivp
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall, solve_coupled_wall, potential_and_hessian
from perfectpower import wall_jost_scattering as ws

MODEL = WallModel(30000., .1, .025000033333333335, 300000., 3000.)


class Propagators(unittest.TestCase):
    def test_johnson_is_fourth_order_against_independent_ode(self):
        q, R = .7, 6.
        V = lambda x: -3/np.cosh(x)**2
        ref = []
        for bc in [(0., 1.), (1., 0.)]:
            s = solve_ivp(lambda x, z: [z[1], (V(x) - q*q)*z[0]], (0, R), bc, rtol=1e-13, atol=1e-14, method='DOP853')
            ref.append(s.y[1, -1]/s.y[0, -1])
        errors = []
        for n in (200, 400):
            rho = np.linspace(0, R, n + 1)
            H = np.zeros((n + 1, 3, 3)); H[:, 0, 0] = H[:, 1, 1] = V(rho); H[:, 2, 2] = 1.
            y = ws._johnson(np.diag([1e30, 0, 1e30]).astype(complex)[None], rho, H, np.array([q*q + 0j]))[0]
            errors.append(max(abs(y[0, 0] - ref[0]), abs(y[1, 1] - ref[1])))
        self.assertLess(errors[0], 3e-7)
        self.assertGreater(errors[0]/errors[1], 14)

    def test_vectorised_hessian_matches_pointwise_definition(self):
        w = solve_coupled_wall(MODEL, HiggsWall())
        rho = np.array([0., .3, 2., 7., 40., 900.])
        z = w['solution'].sol(rho)
        H = ws.hessian(w, rho)
        for j in range(len(rho)):
            np.testing.assert_allclose(H[j], potential_and_hessian(MODEL, HiggsWall(), *z[:3, j])[1], rtol=1e-13, atol=1e-25)
        mu, V = ws.vacuum_channels(w)
        np.testing.assert_allclose(V.T@V, np.eye(3), atol=1e-14)
        self.assertAlmostEqual(sqrt(mu[0])*30000, 125.4358800343, places=6)

    def test_reference_tail_exact_for_constant_vacuum(self):
        w = solve_coupled_wall(MODEL, HiggsWall())
        E = np.array([.3 + 0j])
        mu, V = ws.vacuum_channels(w)
        Y0 = (V@np.diag([.2, -.1, 3.])@V.T).astype(complex)[None]
        L = w['L']
        a = ws._reference_tail(Y0, np.linspace(L + 10, L + 20, 3), w, E, 1., False)
        b = ws._reference_tail(Y0, np.linspace(L + 10, L + 20, 401), w, E, 1., False)
        np.testing.assert_allclose(a, b, atol=1e-12)
        with self.assertRaises(ValueError):
            ws._reference_tail(Y0, np.array([L + 10, L + 60]), w, E, 1., False)

    def test_unknown_sector_rejected(self):
        w = solve_coupled_wall(MODEL, HiggsWall())
        with self.assertRaises(ValueError):
            ws.jost_function(w, 'even', [.1])


class DecoupledLimits(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pt = solve_coupled_wall(replace(MODEL, current_g_GeV=0.), HiggsWall(portal=0.))

    def test_poschl_teller_reflectionless_transmission(self):
        k = self.pt['k']
        E = np.array([.25, 1.])
        _, St = ws.s_matrix(self.pt, 'translation', E, R=300.)
        _, So = ws.s_matrix(self.pt, 'opposite', E, R=300.)
        for e, a, b in zip(E, St, So):
            fl = ws.full_line(a['S'], b['S'])
            q = sqrt(e - 4*k*k)
            t = (q + 1j*k)*(q + 2j*k)/((q - 1j*k)*(q - 2j*k))
            self.assertLess(abs(-fl['transmission'][1, 1] - t), 1e-8)
            self.assertLess(abs(fl['reflection'][1, 1]), 1e-8)
            self.assertLess(abs(fl['transmission'][0, 0] - 1), 1e-8)
            self.assertLess(fl['unitarity_defect'], 1e-13)

    def test_exact_translation_and_shape_poles(self):
        z0 = ws.find_pole(self.pt, 'translation', 1e-6, R=300.)[0]
        z1 = ws.find_pole(self.pt, 'opposite', .149, R=300.)[0]
        self.assertLess(abs(z0), 1e-11)
        self.assertLess(abs(z1 - .15), 1e-11)


class ShapeResonance(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.wall = solve_coupled_wall(MODEL, HiggsWall())
        cls.state = ws.shape_bound_state(cls.wall)
        cls.se = ws.higgs_green_self_energy(cls.wall, cls.state)

    def test_fem_and_jost_agree_on_decoupled_shape_state(self):
        Eb = ws.find_pole(self.wall, 'opposite', .15, decouple=True)[0]
        self.assertLess(abs(Eb - self.state['E']), 1e-11)
        self.assertLess(self.state['E'], .15)
        self.assertGreater(self.state['E'], ws.vacuum_channels(self.wall)[0][0])

    def test_width_by_green_function_golden_rule_and_closed_form(self):
        G = -2*self.se['Sigma'].imag
        self.assertGreater(G, 0)
        self.assertAlmostEqual(G/self.se['golden_rule_Gamma_E'], 1, places=9)
        an = ws.analytic_shape_width(self.wall)
        self.assertLess(abs(G/an['Gamma_E'] - 1), 1e-3)
        self.assertAlmostEqual(self.se['standing_wave_overlap']/an['standing_wave_overlap'], 1, places=3)
        p = ws.physical_width(self.state['E'], G, 30000.)
        self.assertAlmostEqual(p['Gamma_GeV']*1e13, 3.0608, places=3)

    def test_coupling_ladder_reproduces_second_order_pole(self):
        # Reference energy from the same discretisation as the coupled poles.
        Eb = ws.find_pole(self.wall, 'opposite', self.state['E'], decouple=True)[0]
        for eps in (3e4, 1e5):
            Ep = ws.find_pole(self.wall, 'opposite', Eb + eps**2*self.se['Sigma'], coupling_scale=eps)[0]
            self.assertLess(abs((Ep - Eb)/eps**2 - self.se['Sigma'])/abs(self.se['Sigma']), 1e-5)
            self.assertLess(Ep.imag, 0)

    def test_real_axis_breit_wigner_and_unitarity(self):
        eps = 1e5
        Ep = ws.find_pole(self.wall, 'opposite', self.state['E'] + eps**2*self.se['Sigma'], coupling_scale=eps)[0]
        G = -2*Ep.imag
        E = Ep.real + np.array([-4., -1., 0., 1., 4.])*G
        S = np.array([s['S'][0, 0] for s in ws.s_matrix(self.wall, 'opposite', E, coupling_scale=eps)[1]])
        bg = np.array([s['S'][0, 0] for s in ws.s_matrix(self.wall, 'opposite', E, coupling_scale=eps, decouple=True)[1]])
        np.testing.assert_allclose(abs(S), 1, atol=1e-13)
        np.testing.assert_allclose(S, bg*(E - Ep.conjugate())/(E - Ep), atol=1e-4)

    def test_two_open_channels_unitary_and_mediator_reflection(self):
        _, St = ws.s_matrix(self.wall, 'translation', [.3])
        _, So = ws.s_matrix(self.wall, 'opposite', [.3])
        self.assertEqual(St[0]['open_channels'], [0, 1])
        fl = ws.full_line(St[0]['S'], So[0]['S'])
        self.assertLess(fl['unitarity_defect'], 1e-13)
        r = abs(fl['reflection'][1, 1])**2
        w2 = solve_coupled_wall(replace(MODEL, current_g_GeV=1500.), HiggsWall())
        fl2 = ws.full_line(ws.s_matrix(w2, 'translation', [.3])[1][0]['S'], ws.s_matrix(w2, 'opposite', [.3])[1][0]['S'])
        self.assertAlmostEqual(abs(fl2['reflection'][1, 1])**2/r, 1/16, places=4)


if __name__ == '__main__':
    unittest.main()
