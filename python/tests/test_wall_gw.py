import unittest
import numpy as np
from perfectpower import wall_network as wn


def field(N, amp, k=3):
    z = np.arange(N)[None, None, :]*np.ones((N, N, 1))
    return [(c*np.cos(2*np.pi*k*z/N)).astype(np.float32) for c in amp]


class TTProjection(unittest.TestCase):
    N = 32

    def test_plus_and_cross_polarisations_survive(self):
        # Pairs: xx, yy, zz, xy, xz, yz; wave along z.
        plus = field(self.N, (1, -1, 0, 0, 0, 0))
        cross = field(self.N, (0, 0, 0, 1, 0, 0))
        mp, _, _ = wn.gw_energy_spectrum(plus, 1.)
        mc, _, _ = wn.gw_energy_spectrum(cross, 1.)
        # <u_ij u_ij>: plus has xx^2+yy^2=2 cos^2 -> mean 1; cross counts xy twice -> 1.
        self.assertAlmostEqual(mp, 1., places=5)
        self.assertAlmostEqual(mc, 1., places=5)

    def test_longitudinal_and_trace_removed(self):
        for amp in ((0, 0, 1, 0, 0, 0), (0, 0, 0, 0, 1, 0), (0, 0, 0, 0, 0, 1)):
            m, _, _ = wn.gw_energy_spectrum(field(self.N, amp), 1.)
            self.assertLess(m, 1e-10)
        # Pure trace along x,y (delta_ij - k k) keeps no TT part.
        m, _, _ = wn.gw_energy_spectrum(field(self.N, (1, 1, 0, 0, 0, 0)), 1.)
        self.assertLess(m, 1e-10)

    def test_spectrum_integrates_to_total(self):
        rng = np.random.default_rng(0)
        u = [rng.standard_normal((self.N,)*3).astype(np.float32) for _ in range(6)]
        m, k, s = wn.gw_energy_spectrum(u, 1., nbins=64)
        edges = np.geomspace(2*np.pi/self.N, np.pi*np.sqrt(3), 65)
        self.assertAlmostEqual(np.sum(s*np.log(edges[1:]/edges[:-1]))/m, 1., places=4)


if __name__ == '__main__':
    unittest.main()
