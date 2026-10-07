from math import pi, sqrt
import unittest
import numpy as np
from perfectpower import wall_network as wn


class Lattice(unittest.TestCase):
    def test_planar_kink_is_static_and_has_continuum_tension(self):
        r = wn.lattice_kink_check()
        self.assertLess(abs(r['lattice_final']/r['continuum_two_walls'] - 1), .015)
        self.assertLess(r['max_velocity'], 1e-3)

    def test_area_estimator_on_sphere_and_circle(self):
        N = 96
        x = np.indices((N,)*3) - N/2 + .5
        R = 30.
        f = (np.sqrt((x**2).sum(0)) - R).astype(np.float32)
        self.assertLess(abs(wn.wall_area(f, 1.)/(4*pi*R*R) - 1), .03)
        y = np.indices((400, 400)) - 200 + .5
        g = np.sqrt((y**2).sum(0)) - 150.
        self.assertLess(abs(wn.wall_area(g, 1.)/(2*pi*150) - 1), .01)

    def test_small_network_forms_and_bias_annihilates(self):
        r = wn.evolve(48, seed=3, record_every=5)
        self.assertGreater(r['A'][-1], .4)
        b = wn.evolve(48, seed=3, eps1=4e-3, record_every=5)
        t1, t2 = wn.annihilation_time(b, .8)
        self.assertTrue(np.isfinite(t2) and t2 > 5)
        self.assertTrue(np.isnan(t1) or t1 > b['tau'][np.argmax(b['A'] >= .4)])

    def test_C_ann_conversion(self):
        # t=tau^2/2, DeltaV/sigma=2 eps1/sigma_hat.
        self.assertAlmostEqual(wn.C_ann(10., 1e-3, .5, .8), 50*2e-3/(.8*wn.kink_tension(.5)))
        self.assertAlmostEqual(wn.kink_tension(.5), 2*sqrt(2)/3*sqrt(.5))


if __name__ == '__main__':
    unittest.main()
