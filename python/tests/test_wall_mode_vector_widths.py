import unittest
from math import pi, sqrt
import numpy as np
from numpy.polynomial.legendre import leggauss
from perfectpower import wall_mode_vector_widths as V


def flat_profile(R=30., n=3001, sigma=1.2, amplitude=.7):
    x = np.linspace(0, R, n); w = V.simpson_weights(x)
    vertex = amplitude*np.exp(-x*x/(2*sigma*sigma))
    z = np.zeros_like(x)
    return {'x': x, 'Vw': 2*w*vertex, 'relative_barrier': z, 'a': z, 'L_extra': z, 'h_over_h0': np.ones_like(x)}, sigma, amplitude


def plane_wave_width(M, m1, m2, sigma, amplitude, identical, order=80):
    """Independent vacuum formula: plane waves on R^2 and the covariant polarization sum
    sum|eps1.eps2|^2=2+(K1.K2)^2/(m1^2 m2^2)."""
    a, w = leggauss(order)
    Vt = lambda q: amplitude*sqrt(2*pi)*sigma*np.exp(-q*q*sigma*sigma/2)
    kmax = sqrt((M-m2)**2-m1**2); total = 0.
    for k, wk in zip(kmax*a, kmax*w):
        lmax = sqrt(max((M-sqrt(k*k+m1*m1))**2-m2*m2, 0)); l = lmax*a; wl = lmax*w
        s1 = k*k+m1*m1; s2 = l*l+m2*m2; om1 = (M*M+s1-s2)/(2*M); om2 = M-om1
        p2 = np.maximum(om1*om1-s1, 0); K12 = om1*om2+p2-k*l
        total += wk*np.sum(wl*Vt(k+l)**2/(4*pi*pi)*(2+K12**2/(m1*m1*m2*m2)))
    return (.5 if identical else 1.)*total/(8*M*M)


class VectorWidths(unittest.TestCase):
    def test_exact_identities(self):
        r = V.exact_identities()
        self.assertTrue(all(v == '0' for v in r.values()))
        for key in ['TMn_Proca_equation_z', 'TMn_Proca_charge_density', 'vacuum_completeness_33', 'equivalence_bracket']:
            self.assertIn(key, r)

    def test_vacuum_polarization_sum_against_plane_waves(self):
        prof, sigma, A = flat_profile()
        for M, m1, m2, ident in [(3., .9, .9, True), (3., .7, 1.1, False), (2.5, .3, 1.6, False)]:
            r = V.pair_width_core(prof, M, m1, m2, identical=ident, momentum_nodes=161, order=64)
            ref = plane_wave_width(M, m1, m2, sigma, A, ident)
            self.assertLess(abs(r['width']/ref-1), 2e-6, (M, m1, m2, r['width'], ref))

    def test_closed_channel(self):
        prof, _, _ = flat_profile(n=301)
        self.assertFalse(V.pair_width_core(prof, 2., 1., 1.01, identical=True)['open'])

    def test_te_sector_is_transverse_scalar_width(self):
        # In vacuum with equal masses TE equals the scalar distorted-wave width.
        from perfectpower.wall_pair_decay import parity_continuum, continuum_pair_width
        prof, sigma, A = flat_profile()
        M, m = 3., .8
        r = V.pair_width_core(prof, M, m, m, identical=True, momentum_nodes=161, order=64, kernels_out=True)
        G = np.array([r['kernels']['TT', 0], r['kernels']['TT', 1]])
        ref = continuum_pair_width(M, m, r['grid1'], G, identical=True, order=64)['width_GeV']
        self.assertAlmostEqual(r['sectors']['TE_TE']/ref, 1, places=10)

    def test_declared_widths(self):
        d = V.declared_vector_widths(.65, .36, 246.)
        self.assertAlmostEqual(d['W_mass_GeV'], 79.95, places=10)
        self.assertAlmostEqual(d['W_width_GeV'], 9*.65**2*79.95/(48*pi), places=12)
        self.assertTrue(2.3 < d['Z_width_GeV'] < 2.5)
        q = V.declared_vector_widths(.65, .36, 246., alpha_s=.118)
        self.assertGreater(q['Z_width_GeV'], d['Z_width_GeV'])

    def test_breit_wigner_normalization(self):
        m, G = 80., 2.
        s, w = V._tan_nodes(m, G, 1., 4e4, 400)
        self.assertAlmostEqual(np.sum(w*V.breit_wigner_density(s, m, G, running=False))*pi/(np.arctan((4e4-m*m)/(m*G))-np.arctan((1-m*m)/(m*G))), 1, places=10)
        tot = np.sum(w*V.breit_wigner_density(s, m, G, running=True))
        self.assertLess(abs(tot-1), .05)
        # composite rule: exact for the fixed-width density, and integrates smooth tails
        s2, w2 = V.spectral_nodes(m, G, 1., 4e4, 24)
        ref = (np.arctan((4e4-m*m)/(m*G))-np.arctan((1-m*m)/(m*G)))/pi
        self.assertAlmostEqual(np.sum(w2*V.breit_wigner_density(s2, m, G, running=False)), ref, places=6)
        self.assertAlmostEqual(np.sum(w2*s2), (4e4**2-1)/2, delta=1e-6*4e4**2)

    def test_box_spectrum_free_and_barrier(self):
        x = np.linspace(0, 10, 1001); z = np.zeros_like(x)
        prof = {'x': x, 'scale_GeV': 1., 'relative_barrier': .2/np.cosh(x)**2, 'L_extra': z}
        r = V.box_spectrum({**prof, 'relative_barrier': z}, 1., radius_x=20., dx=.01)
        for key in ['transverse_even', 'transverse_odd']:
            self.assertAlmostEqual(r[key]['levels_above_threshold_GeV2'][0]/r[key]['free_box_levels_GeV2'][0], 1, places=3)
        b = V.box_spectrum(prof, 1., radius_x=20., dx=.01)
        self.assertGreater(b['transverse_even']['levels_above_threshold_GeV2'][0], r['transverse_even']['levels_above_threshold_GeV2'][0])
        s = V.zero_energy_scattering_lengths({**prof, 'h_over_h0': np.ones_like(x), 'a': z}, 1.)
        self.assertGreater(s['transverse_even']['asymptotic_slope'], 0)

    def test_certified_statement_reads_flags(self):
        ok = V.certified_threshold_statement({'P5_Higgs_positive': True, 'Higgs_at_least_vacuum_everywhere': True,
                                              'Higgs_strictly_above_vacuum_interior': True})
        self.assertTrue(ok['hypotheses_certified'])
        bad = V.certified_threshold_statement({'P5_Higgs_positive': True})
        self.assertFalse(bad['hypotheses_certified'])


def broad_mode(M=3., sigma=6., R=70., n=7001, vH=1.):
    """A very broad wall-mode profile approximates a bulk particle at rest."""
    x = np.linspace(0, R, n); phi = (pi*sigma*sigma)**-.25*np.exp(-x*x/(2*sigma*sigma))
    return {'x': x, 'scale_GeV': 1., 'M_GeV': M, 'v_H_GeV': vH, 'psi_H_canonical': phi,
            'quadrature_weights': V.simpson_weights(x)}


class BulkLimit(unittest.TestCase):
    """Broad profiles reproduce textbook 3+1 Higgs decay widths with O(1/(M sigma)^2) error."""
    def errors(self, sigma, R, n, order):
        P = broad_mode(sigma=sigma, R=R, n=n); M, mf, m, vH = 3., .4, .8, 1.
        f = V.fermion_pair_width(P, mf, 3, order=order)['width_GeV']
        f_ref = 3*M*mf*mf/(8*pi*vH*vH)*(1-4*mf*mf/(M*M))**1.5
        g = V.gluon_pair_width(P, .1, order=order)['width_GeV']; g_ref = .01*M**3/(72*pi**3*vH*vH)
        z = np.zeros_like(P['x'])
        prof = {'x': P['x'], 'Vw': 2*P['quadrature_weights']*(2*m*m/vH)*P['psi_H_canonical'],
                'relative_barrier': z, 'a': z, 'L_extra': z, 'h_over_h0': np.ones_like(z)}
        x = m*m/(M*M); ref = M**3/(32*pi*vH*vH)*sqrt(1-4*x)*(1-4*x+12*x*x)
        w = V.pair_width_core(prof, M, m, m, identical=False, momentum_nodes=129, order=order)['width']
        zz = V.pair_width_core(prof, M, m, m, identical=True, momentum_nodes=129, order=order)['width']
        return np.array([f/f_ref-1, g/g_ref-1, w/(2*ref)-1, zz/ref-1])

    def test_bulk_limit(self):
        e4 = self.errors(4., 40., 2001, 200); e8 = self.errors(8., 70., 3501, 300)
        self.assertTrue(np.all(abs(e8) < 3e-3), e8)
        ratio = e4/e8
        self.assertTrue(np.all((ratio > 3.5) & (ratio < 4.5)), ratio)


class Candidate(unittest.TestCase):
    """Actual wall candidate at coarse resolution (about 10 s)."""
    @classmethod
    def setUpClass(cls):
        from perfectpower.dimensionful_walls import WallModel
        from perfectpower.wall_fluctuations import HiggsWall
        from perfectpower.wall_gauge_channels import candidate_channel_solution
        cls.sol = candidate_channel_solution(WallModel(30000, .1, .025, 300000, 3000), HiggsWall())
        cls.prof = V.candidate_profile(cls.sol, spatial_nodes=1301)

    def test_te_matches_main_and_equivalence_and_threshold(self):
        r = V.vector_pair_widths(self.prof, .16, identical=False, momentum_nodes=97, order=32)
        self.assertLess(abs(r['TE_GeV']/9.20148937628e-10-1), 1e-3)
        self.assertGreater(r['width_GeV'], 5*r['TE_GeV'])
        from perfectpower.wall_pair_decay import candidate_pair_data
        gold = candidate_pair_data(self.sol, channel='global_Goldstone', momentum_nodes=97, spatial_nodes=1301, order=32)['width_GeV']
        eq = V.goldstone_equivalence_scan(self.prof, [.0125**2, .00625**2, .003125**2], gold, momentum_nodes=97, order=32)
        self.assertLess(abs(eq['extrapolation']['extrapolated_ratio']-1), 2e-3)
        closed = V.vector_pair_widths(self.prof, .65**2, identical=False, momentum_nodes=97, order=32)
        self.assertFalse(closed['open'])
        spec = V.box_spectrum(self.prof, 79.95, radius_x=88., dx=.017)
        self.assertTrue(all(v['levels_above_threshold_GeV2'][0] > 0 for k, v in spec.items() if isinstance(v, dict)))


if __name__ == '__main__':
    unittest.main()
