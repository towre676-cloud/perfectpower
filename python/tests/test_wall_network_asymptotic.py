import unittest
from math import sqrt, pi
import numpy as np
from perfectpower import wall_network as wn
from perfectpower import wall_annihilation_gw as wa
from perfectpower import wall_network_asymptotic as wna


class Mapping(unittest.TestCase):
    def test_width_and_bias_map_to_constant_physical_ratio(self):
        X = 700.
        for s in (0., .3, .5, 1.):
            lam = wna.lam_for(s, 2., 50.)
            self.assertAlmostEqual(sqrt(2/lam)*50.**(-s), 2., places=12)
            for tau in (3., 17., 90.):
                e = wna.bias_e(tau, s, lam, X)
                # bias pressure tau^2s (4e/3) over curvature-force coefficient sigma0 tau^s equals tau/X
                self.assertAlmostEqual(tau**(2*s)*(4*e/3)/(wna.sigma0(lam)*tau**s), tau/X, places=12)
        self.assertAlmostEqual(wna.predicted_tau_ann(800., 1.8), sqrt(2*1.8*800.), places=12)

    def test_s1_reproduces_physical_biased_evolution_with_tensors(self):
        N, eps = 16, 2e-4
        a = wa.evolve_biased_gw(N, eps=eps, tau_on=12., ramp=3., tau_ref=16., tau_f=20., measure_every=2.)
        lam = a['lam']
        X = .75*wn.kink_tension(lam)/eps
        b = wna.evolve(N, s=1., w_ref=2., tau_ref=16., X=X, tau_on=12., ramp=3., tau_i=10., tau_f=20., gw=True,
                       measure_every=2.)
        self.assertAlmostEqual(b['lam'], lam, places=15)
        self.assertEqual(len(a['rows']), len(b['rows']))
        for x, y in zip(a['rows'], b['rows']):
            self.assertAlmostEqual(x['tau'], y['tau'], places=9)
            self.assertAlmostEqual(x['A'], y['A'], places=6)
            self.assertAlmostEqual(x['false_fraction'], y['false_fraction'], places=9)
            self.assertLess(abs(x['rho_gw']/y['rho_gw'] - 1), 1e-4)

    def test_s0_unbiased_reproduces_prs_network(self):
        a = wn.evolve(24, lam=.5, tau_f=12., seed=3, record_every=5)
        b = wna.evolve(24, s=0., w_ref=2., tau_ref=1., tau_f=12., seed=3, measure_every=1.)
        self.assertEqual(len(a['A']), len(b['rows']))
        for A, y in zip(a['A'], b['rows']):
            self.assertLess(abs(A - y['A']), 2e-3*max(A, .1))

    def test_uniform_vacua_static_and_metastability_guard(self):
        for s in (0., .5):
            for v in (1., -1.):
                r = wna.evolve(6, s=s, w_ref=2., tau_ref=4., X=50., tau_f=8., field=np.full((6,)*3, v), return_field=True)
                self.assertLess(float(abs(r['field'] - v).max()), 1e-6)
        with self.assertRaises(ValueError):
            wna.evolve(6, s=0., w_ref=2., tau_ref=1., X=.01, tau_f=4., field=np.full((6,)*3, .5))


class PlanarWall(unittest.TestCase):
    def test_biased_planar_wall_follows_thin_wall_law_for_every_s(self):
        """(gamma v)'+3 gamma v/tau=tau/X: the PRS momentum condition makes the motion s-independent."""
        N, X, ti, tf = 96, 300., 10., 30.
        x = np.arange(N) + .5
        for s in (0., .5, 1.):
            lam = wna.lam_for(s, 2., 30.)
            w = sqrt(2/lam)*ti**(-s)
            prof = np.tanh((x - N/4)/w)*np.tanh((x - 3*N/4)/w)
            field = np.repeat(np.repeat(prof[:, None, None], 2, 1), 2, 2)
            r = wna.evolve(N, s=s, w_ref=2., tau_ref=30., X=X, tau_i=ti, tau_f=tf, dt=.05, field=field,
                           measure_every=5., return_field=True)
            f = r['field'][:, 0, 0]
            j = int(np.flatnonzero((f[:-1] > 0) & (f[1:] <= 0))[0])
            z = x[j] + f[j]/(f[j] - f[j + 1])
            moved = z - N/4
            ode = wna.thin_wall_displacement(X, ti, tf)
            self.assertGreater(ode, 3.)
            self.assertLess(abs(moved - ode), .25, (s, moved, ode))  # 0.06-0.15 observed (finite width)


class Analysis(unittest.TestCase):
    def test_fits_recover_synthetic_laws(self):
        X = np.array([200., 400., 800., 1600., 3200.])
        tau = np.sqrt(2*1.9*X)
        p, c, se = wna.fit_power(X, tau)
        self.assertAlmostEqual(p, .5, places=10)
        K, t0, _ = wna.fit_offset(X, np.sqrt(2*(1.9*X + 300.)))
        self.assertAlmostEqual(K, 1.9, places=8); self.assertAlmostEqual(t0, 300., places=5)
        q, Kq, t0q = wna.fit_power_with_offset(X, np.sqrt(2*(1.9*X + 100.)))
        self.assertAlmostEqual(q, 1., places=6); self.assertAlmostEqual(Kq, 1.9, places=5)
        xm, pl = wna.local_exponents(X[::-1], tau[::-1])
        np.testing.assert_allclose(pl, .5, atol=1e-12)
        np.testing.assert_allclose(xm, np.sqrt(X[1:]*X[:-1]), rtol=1e-12)

    def test_annihilation_tau_interpolates(self):
        rows = [{'tau': t, 'false_fraction': f} for t, f in ((1., .5), (2., .3), (3., .02), (4., .0))]
        self.assertAlmostEqual(wna.annihilation_tau(rows, 0.), 3.5, places=12)
        self.assertTrue(np.isnan(wna.annihilation_tau(rows[:3], 0.)))

    def test_spectrum_shape_reads_broken_power_law(self):
        k = np.geomspace(.01, 3., 60)
        kp = .2
        s = np.where(k < kp, (k/kp)**3, (k/kp)**-1.)
        sh = wna.spectrum_shape(k, s, tau=10.)
        self.assertAlmostEqual(sh['IR_slope'], 3., places=6)
        self.assertAlmostEqual(sh['UV_slope'], -1., places=6)
        self.assertAlmostEqual(sh['peak_f_over_H'], sh['peak_k']*10/(2*pi), places=12)
        self.assertGreater(sh['peak_over_box'], 15)

    def test_log_parabola_peak_finds_off_grid_maximum(self):
        k = np.geomspace(.01, 3., 48)
        kp = .1234
        s = np.exp(-.5*(np.log(k/kp)/.6)**2)  # exact parabola in log-log
        self.assertAlmostEqual(wna.peak_log_parabola(k, s), kp, places=10)
        self.assertTrue(np.isnan(wna.peak_log_parabola(k, k**-1.)))  # maximum at the edge


if __name__ == '__main__':
    unittest.main()
