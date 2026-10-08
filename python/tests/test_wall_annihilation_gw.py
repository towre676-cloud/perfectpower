import unittest
from math import pi, sqrt
import numpy as np
from perfectpower import wall_network as wn
from perfectpower import wall_annihilation_gw as wa


class Stencils(unittest.TestCase):
    def test_laplacian_and_gradient_match_roll_versions(self):
        f = np.random.default_rng(1).standard_normal((12, 10, 8)).astype(np.float32)
        out = np.empty_like(f)
        np.testing.assert_allclose(wa.laplacian_into(f, out), wn.laplacian(f, 1.), atol=1e-5)
        ref = wn._gradients(f, 1.)
        for ax in range(3):
            np.testing.assert_allclose(wa.gradient_into(f, ax, np.empty_like(f)), ref[ax], atol=1e-6)


class Potential(unittest.TestCase):
    def test_cubic_bias_keeps_minima_and_splits_by_four_thirds_eps(self):
        lam, eps = 1e-3, 2e-4
        p = wa.potential_parameters(lam, eps)
        V = lambda x: lam/4*(x*x - 1)**2 + eps*(x**3/3 - x)
        dV = lambda x: (x*x - 1)*(lam*x + eps)
        self.assertEqual(dV(1.), 0.); self.assertEqual(dV(-1.), 0.)
        self.assertAlmostEqual(V(-1.) - V(1.), p['DeltaV'], places=15)
        self.assertAlmostEqual(p['DeltaV'], 4*eps/3, places=15)
        d2V = lambda x: lam*(3*x*x - 1) + 2*eps*x
        self.assertGreater(d2V(-1.), 0); self.assertGreater(d2V(1.), d2V(-1.))  # metastable false vacuum
        with self.assertRaises(ValueError):
            wa.potential_parameters(lam, lam)

    def test_uniform_vacua_are_static_with_bias(self):
        for v in (1., -1.):
            r = wa.evolve_biased_gw(8, eps=1e-4, tau_ref=8., tau_on=10., ramp=0., tau_f=14., gw=False, measure_every=1.,
                                    field=np.full((8,)*3, v))
            self.assertTrue(all(abs(x['mean_phi'] - v) < 1e-6 for x in r['rows']))

    def test_ramp(self):
        self.assertEqual(wa.bias_ramp(5., 10., 4.), 0.)
        self.assertEqual(wa.bias_ramp(14., 10., 4.), 1.)
        self.assertAlmostEqual(wa.bias_ramp(12., 10., 4.), .5)


class Evolution(unittest.TestCase):
    def test_zero_bias_reproduces_evolve_physical_gw(self):
        a = wn.evolve_physical_gw(20, tau_f=18., measure_every=2.)
        b = wa.evolve_biased_gw(20, tau_f=18., measure_every=2., tau_ref=18.)
        self.assertEqual(len(a['rows']), len(b['rows']))
        for x, y in zip(a['rows'], b['rows']):
            self.assertAlmostEqual(x['A'], y['A'], places=9)
            self.assertLess(abs(x['rho_gw']/y['rho_gw'] - 1), 1e-4)

    def test_tt_kinetic_matches_wall_network_and_gradient_part_of_plane_wave(self):
        N, k = 16, 3
        z = np.arange(N)[None, None, :]*np.ones((N, N, 1))
        c = np.cos(2*pi*k*z/N).astype(np.float32)
        plus = [c, -c, 0*c, 0*c, 0*c, 0*c]
        hk, hg, kc, sk, sg = wa.tt_spectra(plus, plus)
        m, _, _ = wn.gw_energy_spectrum(plus, 1.)
        self.assertAlmostEqual(hk, m, places=5)
        self.assertAlmostEqual(hg/hk, (2*np.sin(pi*k/N))**2, places=5)

    def test_free_tensor_wave_keeps_rho_a4(self):
        N, k = 16, 4
        kz = 2*pi*k/N; keff = 2*np.sin(kz/2)
        z = np.arange(N)[None, None, :]*np.ones((N, N, 1))
        tau0 = 10.
        # outgoing solution u=sin(k(tau)) /tau: u'=(k cos - sin/tau)/tau
        u = (np.sin(kz*z)*0 + np.cos(kz*z)*np.sin(keff*tau0)/tau0).astype(np.float32)
        du = (np.cos(kz*z)*(keff*np.cos(keff*tau0) - np.sin(keff*tau0)/tau0)/tau0).astype(np.float32)
        zero = np.zeros_like(u)
        r = wa.evolve_biased_gw(N, field=np.ones((N,)*3), tensors=([u, -u, zero, zero, zero, zero], [du, -du, zero, zero, zero, zero]),
                                tau_i=tau0, tau_f=50., dt=.02, tau_ref=16., measure_every=2.)
        t = np.array([x['tau'] for x in r['rows']])
        E = np.array([x['rho_gw_avg']*x['tau']**4 for x in r['rows']])
        # exact a^4 rho for u=sin(k tau)/tau: [(k cos - sin/tau)^2 + k^2 sin^2]; the 1/(k tau) terms die off
        Eth = (keff*np.cos(keff*t) - np.sin(keff*t)/t)**2 + keff**2*np.sin(keff*t)**2
        ratio = E/Eth
        self.assertLess(ratio.std()/ratio.mean(), .02)  # residual: u' lags u by dt/2 in the leapfrog (error ~ k dt/2)
        self.assertLess(abs(E[-5:].mean()/E[:5].mean() - 1), .05)
        Ek = np.array([x['rho_gw']*x['tau']**4 for x in r['rows']])
        self.assertGreater(Ek.std()/Ek.mean(), .1)  # kinetic part alone oscillates

    def test_small_biased_network_annihilates_and_unbiased_does_not(self):
        kw = dict(tau_ref=16., tau_on=12., tau_i=4., tau_f=36., gw=False, measure_every=1.)
        b = wa.evolve_biased_gw(32, eps=4e-4, **kw)
        u = wa.evolve_biased_gw(32, eps=0., **kw)
        t_ff, _ = wa.annihilation_times(b['rows'], .8, 12.)
        self.assertTrue(12. < t_ff < 36.)
        self.assertTrue(np.isnan(wa.annihilation_times(u['rows'], .8, 12.)[0]))


class Analysis(unittest.TestCase):
    def test_power_law_fit_and_pressure_balance(self):
        x = np.array([10., 20., 40., 80.])
        p, c, se = wa.power_law_fit(x, 3*x**.5)
        self.assertAlmostEqual(p, .5, places=10); self.assertAlmostEqual(c, 3., places=10)
        self.assertAlmostEqual(wa.pressure_balance_tau(2., 1., 1.8), sqrt(7.2))

    def test_annihilation_time_interpolates(self):
        rows = [{'tau': t, 'A': 1., 'false_fraction': f} for t, f in ((10, .5), (20, .5), (30, .11), (40, .01 - .02))]
        rows[-1]['false_fraction'] = 0.
        t, _ = wa.annihilation_times(rows, .8, 15.)
        self.assertAlmostEqual(t, 30 + (.11 - .01)/.11*10)


if __name__ == '__main__':
    unittest.main()
