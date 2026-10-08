import unittest
from math import sqrt, pi
import numpy as np
from scipy.integrate import quad
from perfectpower import wall_mode_lifetime as W


class Couplings(unittest.TestCase):
    def test_reduced_couplings(self):
        c = W.couplings()
        self.assertAlmostEqual(c['cH']*c['h02'], 2*.13*(246/30000)**2/W.CANDIDATE['source_lambda'], places=12)
        self.assertAlmostEqual(c['ck'], 1e-7/c['k']**2, places=14)
        self.assertAlmostEqual(c['Higgs_mass2'], 2*c['cH']*c['h02'], places=12)
        self.assertAlmostEqual(c['hbar_Higgs'], c['hbar_source']/c['h02'], places=12)
        with self.assertRaises(ValueError):W.couplings(v_GeV=-1)

    def test_closed_form_second_harmonic_constant(self):
        self.assertAlmostEqual(W.kink_second_harmonic_rate(), 9*sqrt(6)/4*pi**2/np.sinh(sqrt(2)*pi)**2, places=15)
        self.assertAlmostEqual(W.kink_second_harmonic_rate(), .0301092, places=6)


class Lattice(unittest.TestCase):
    def test_fourth_order_laplacian_and_weighted_symmetry(self):
        errs = []
        for dx in (.2, .1):
            N = int(round(40/dx)); x = dx*np.arange(N)
            for par, f, d2 in ((1, np.exp(-x*x), (4*x*x-2)*np.exp(-x*x)), (-1, x*np.exp(-x*x), (4*x**3-6*x)*np.exp(-x*x))):
                errs.append(abs(W.laplacian_matrix(N, dx, par)@f-d2)[:N-4].max())
                g = W._lap(f, dx, par, 0.)
                self.assertLess(abs(g-W.laplacian_matrix(N, dx, par)@f).max(), 1e-11)
        self.assertGreater(errs[0]/errs[2], 12)  # fourth order: ratio ~16
        A = W.laplacian_matrix(30, .3, 1).toarray(); w = np.ones(30); w[0] = .5
        self.assertLess(abs(w[:, None]*A-(w[:, None]*A).T).max(), 1e-12)

    def test_static_wall_discrete_Ward_identity_and_mode(self):
        c = W.couplings(); dx = .25; wall = W.static_wall(c, 120, dx)
        self.assertLess(wall['residual'], 1e-11)
        # Goldstone operator annihilates the Higgs profile on the lattice.
        self.assertLess(wall['Ward_zero_mode_residual'], 1e-11)
        m = W.localized_mode(c, wall, dx)
        self.assertLess(abs(m['omega2']-3), 2e-3)
        self.assertLess(m['linear_leak_energy_rate'], 1e-11)
        self.assertLess(abs(m['canonical_norm']-1), 1e-6)

    def test_classical_Goldstones_stay_zero_and_static_wall_is_static(self):
        c = W.couplings(); dx = .25; wall = W.static_wall(c, 120, dx); m = W.localized_mode(c, wall, dx)
        r = W.classical_statistical_run(c, wall, m, .1, dt=.05, steps=300, samples=1, noise_fraction=0., seed=0, record=(300,))
        self.assertEqual(float(r[300][0]), 0.)
        bg = W.evolve_background(c, wall, m, 0., dt=.05, steps=400)
        self.assertLess(abs(bg['X']-bg['X'][0]).max(), 1e-15)


class PairEmission(unittest.TestCase):
    def free_drive(self, parity, p=.5, Omega=2., eps=.05):
        dx, L, dt = .25, 40., .05; N = int(round(L/dx)); x = dx*np.arange(N)
        wall = {'x': x, 'X': np.zeros(N)}; c = {'cH': 1.}
        steps = 1300; t = dt*np.arange(steps+1)
        X = eps*np.exp(-x*x)[None, :]*np.cos(Omega*t)[:, None]
        nT = int(round(2*pi/Omega/dt))
        r = W.goldstone_pair_power(c, wall, X, dt=dt, p=p, parity=parity, window=(300, 1300, nT), ramp_steps=200)
        return r['power']

    def golden_rule(self, parity, p=.5, Omega=2., eps=.05):
        sgn = 1 if parity == 1 else -1
        def cc(k, l):return eps*(np.exp(-(k-l)**2/4)+sgn*np.exp(-(k+l)**2/4))/(2*sqrt(pi))
        kmax = sqrt((Omega-p)**2-p*p)
        def f(k):
            w1 = sqrt(k*k+p*p); w2 = Omega-w1; l = sqrt(max(w2*w2-p*p, 0.))
            return cc(k, l)**2/(w1*l) if l > 0 else 0.
        # substitution k=kmax sin(s) removes the inverse-square-root endpoint
        I = quad(lambda s:f(kmax*np.sin(s))*kmax*np.cos(s), 0, pi/2, limit=200, epsabs=1e-14)[0]
        return Omega*pi/16*I

    def test_real_time_power_matches_golden_rule_both_parities(self):
        for parity in (1, -1):
            ratio = self.free_drive(parity)/self.golden_rule(parity)
            self.assertLess(abs(ratio-1), .01, msg=f'parity {parity} ratio {ratio}')

    def test_undriven_vacuum_energy_is_exactly_stationary(self):
        dx = .25; N = 100; x = dx*np.arange(N); wall = {'x': x, 'X': np.zeros(N)}
        X = np.zeros((401, N))
        r = W.goldstone_pair_power({'cH': 1.}, wall, X, dt=.05, p=.3, parity=1, window=(100, 400, 30))
        self.assertLess(abs(r['power']), 1e-12)
        with self.assertRaises(ValueError):
            W.goldstone_pair_power({'cH': 1.}, wall, X, dt=.05, p=.3, parity=1, window=(100, 500, 30))


if __name__ == '__main__':unittest.main()
