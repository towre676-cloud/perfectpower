import unittest
try:
    from flint import arb, acb
    from perfectpower import genus2_certified_periods as g
    HAVE_FLINT = True
except ImportError:
    HAVE_FLINT = False


@unittest.skipUnless(HAVE_FLINT, 'python-flint (Arb) not installed')
class CertifiedGenusTwo(unittest.TestCase):
    def test_riemann_relations_are_certified(self):
        pm = g.period_matrix([1, 4, 9])
        self.assertTrue(pm['symmetry_defect'].contains(0))
        self.assertTrue(pm['Im_trace'] > 0 and pm['Im_det'] > 0)
        self.assertLess(float(pm['Omega'][0, 0].rad()), 1e-50)

    def test_integral_cycle_map_and_polarization(self):
        cm = g.cycle_map([2, 3, 7])
        self.assertEqual(g.polarization_identity(cm['maps'], 1, 1, 1), 0)
        self.assertGreater(g.polarization_identity(cm['maps'], 1, -1, 1), 0)
        oq = g.omega_from_quotients([2, 3, 7])
        pm = g.period_matrix([2, 3, 7])
        for i in range(2):
            for j in range(2):
                self.assertTrue((pm['Omega'][i, j] - oq['Omega'][i, j]).contains(0))
        self.assertTrue((pm['Omega'][0, 0] - 2*pm['Omega'][0, 1]).contains(0))

    def test_agm_and_contour_deformation(self):
        W = g.cycle_map([1, 4, 9])['E1_lattice']
        I12, I23 = g.agm_periods(1, 4, 9)
        self.assertTrue((abs(W[0])/2 - I12).contains(0))
        self.assertTrue((abs(W[1])/2 - I23).contains(0))
        roots = g.genus2_roots([1, 4, 9])
        d = g.segment_integral(roots, 3, 1) - g.loop_integral(roots, 3, 1, .9)
        self.assertLess(float(d.abs_upper()), 1e-50)
        with self.assertRaises(ValueError):
            g.loop_integral(roots, 3, 1, 3.)

    def test_node_monodromy_is_T_v_squared(self):
        rows = g.picard_lefschetz([1e-4, 1e-6, 1e-8])
        r = [x['regularised'] for x in rows]
        self.assertLess(float(abs(r[2] - r[1]).mid()), 2e-6)
        self.assertLess(float(abs(r[1] - r[0]).mid()), 2e-4)
        half = [x['half_coefficient'] for x in rows]
        self.assertGreater(float(abs(half[2] - half[1]).mid()), .5)
        self.assertAlmostEqual(float(rows[-1]['fitted_coefficient_over_P5_2pii'].real.mid()), -2., places=5)


if __name__ == '__main__':
    unittest.main()
