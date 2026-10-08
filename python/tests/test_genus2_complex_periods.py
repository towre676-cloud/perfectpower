import unittest
try:
    from flint import arb, acb
    from perfectpower import genus2_certified_periods as g
    from perfectpower import genus2_complex_periods as c
    HAVE_FLINT = True
except ImportError:
    HAVE_FLINT = False

F_C = [-10, -4, -7, -2, 4, 2, 1]  # (x^2-2)(x^2+1)(x^2+2x+5)


@unittest.skipUnless(HAVE_FLINT, 'python-flint (Arb) not installed')
class ComplexGenusTwo(unittest.TestCase):
    def test_model_intersections_and_symplectic_reduction(self):
        C5 = c.model_intersection_matrix()
        self.assertEqual(C5, g.chain_intersection(1))
        T = c.symplectic_basis([r[:4] for r in C5[:4]])
        self.assertEqual(T, [[1, 0, 0, 0], [1, 0, 1, 0], [0, 1, 0, 0], [0, 0, 0, 1]])

    def test_mobius_model_is_exact(self):
        gco, G = c.mobius_model([0, -1, 0, 0, 0, 1], (2, 1, 1, 0))
        self.assertEqual(len(gco), 7)
        self.assertEqual(gco[0], 0)  # t=0 is the image of infinity
        self.assertEqual(G, [[0, -1], [-1, -2]])

    def test_real_branch_points_reproduce_existing_periods(self):
        pm = c.periods_of_polynomial([-36, 0, 49, 0, -14, 0, 1])
        old = g.genus2_cycle_periods([1, 4, 9])
        for p in (0, 1):
            for j in range(5):
                self.assertTrue((pm['cycle_periods'][p][j] - old[p][j]).contains(0))
        pmb = c.periods_of_polynomial([-36, 0, 49, 0, -14, 0, 1], basis=[list(v[:4]) for v in g.BASIS.values()])
        self.assertTrue(c.matrices_close(pmb['Omega'], g.period_matrix([1, 4, 9])['Omega']))

    def test_x6_minus_1_closed_form_and_automorphism(self):
        pm = c.periods_of_polynomial([-1, 0, 0, 0, 0, 0, 1])
        self.assertTrue(c.riemann_certified(pm))
        z = (acb(0, 1)*arb.pi()/3).exp()
        M, rad, symp = c.automorphism_action(pm, [z, z*z])
        self.assertTrue(symp)
        self.assertEqual(c.int_charpoly(M), [1, 0, 1, 0, 1])
        self.assertEqual(c.int_matpow(M, 6), [[int(i == k) for k in range(4)] for i in range(4)])
        Om = pm['Omega']
        s3 = arb(3).sqrt()/2
        self.assertTrue(Om[0, 0].real.contains(-1) and Om[0, 0].imag.contains(s3))
        self.assertTrue(Om[0, 1].real.contains(arb(1)/2) and Om[0, 1].imag.contains(0))
        sols, good = c.siegel_fixed_points(M)
        self.assertEqual(len(good), 1)

    def test_conjugate_pairs_riemann_and_arc_independence(self):
        pm = c.periods_of_polynomial(F_C)
        self.assertTrue(c.riemann_certified(pm))
        self.assertTrue(all(x.contains(0) for x in pm['relation_135']))
        pm2 = c.periods_of_polynomial(F_C, order='im_re')
        M, rad, symp = c.integral_relation(pm['Pi'], pm2['Pi'])
        self.assertTrue(symp)
        self.assertTrue(c.matrices_close(c.omega_of(c.apply_matrix(pm['Pi'], M)), pm2['Omega']))
        bad = c.periods_of_polynomial(F_C, sign_flip=1)
        self.assertFalse(c.integral_relation(pm['Pi'], bad['Pi'])[2])
        self.assertFalse(c.riemann_certified(bad))

    def test_quintic_mobius_consistency(self):
        f = [1, -1, 0, 0, 0, 1]  # x^5-x+1
        p0 = c.periods_of_polynomial(f, mobius=(0, 1, 1, 0))
        p1 = c.periods_of_polynomial(f, mobius=(3, 1, 1, -1))
        self.assertTrue(c.riemann_certified(p0) and c.riemann_certified(p1))
        M, rad, symp = c.integral_relation(p0['Pi'], p1['Pi'])
        self.assertTrue(symp)
        with self.assertRaises(ValueError):
            c.periods_of_polynomial(f)

    def test_arc_certificate_rejects_crossing(self):
        e = [acb(0), acb(2, 2), acb(2), acb(0, 2)]  # 0->2+2i->2->2i crosses itself
        with self.assertRaises(ArithmeticError):
            c.simple_arc_certificate(e)


if __name__ == '__main__':
    unittest.main()
