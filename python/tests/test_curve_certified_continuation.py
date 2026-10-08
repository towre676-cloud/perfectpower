import copy
import unittest
from fractions import Fraction as Q
from perfectpower import bernstein_boxes as B
from perfectpower import metric_boxes_refined as MR

try:
    from flint import arb, acb, acb_mat, ctx
    from perfectpower import legendre_certified_connection as L
    HAVE_FLINT = True
except ImportError:  # pragma: no cover
    HAVE_FLINT = False

BOX = [0, 1, -10**100, 10**100]


class AffineFaceRefinementTests(unittest.TestCase):
    def test_all_36_unresolved_decided(self):
        unresolved = 0
        for d, power, a, eqs in MR.corpus():
            if B.solve_affine_faces(eqs, BOX)['complete']:
                continue
            unresolved += 1
            p = MR.refine(eqs, BOX)
            self.assertTrue(MR.verify(p))
            self.assertTrue(p['face_only_certified_false'])
            self.assertFalse(p['face_only_property'])
            brute = [[x, y] for x in [0, 1] for y in range(-2, 3) if all(B.evaluate(q, x, y) == 0 for q in eqs)]
            self.assertEqual(p['models'], brute)
            if a == 1 and d == power or a == -1 and d == power:
                self.assertEqual(p['route'], 'identical_vanishing_graph')
            else:
                self.assertEqual((a, p['route']), (2, 'sturm_isolation'))
        self.assertEqual(unresolved, 36)

    def test_exact_interior_witness(self):
        eqs = [[(0, 4, 1), (4, 0, -1)], [(0, 1, -1), (1, 0, -1)]]
        p = MR.refine(eqs, BOX)
        c = p['face_only_certificate']
        x, y = Q(c['x']), Q(c['y'])
        self.assertTrue(0 < x < 1 and all(B.evaluate(q, x, y) == 0 for q in eqs))

    def test_irrational_root_ball(self):
        p = MR.refine([[(0, 3, 1), (5, 0, -1)], [(0, 1, 2), (1, 0, -1)]], BOX)
        root = p['face_only_certificate']['root']
        self.assertTrue(root['newton_contraction'])
        lo, hi = map(Q, root['isolating_interval'])
        self.assertTrue(lo*lo < Q(1, 8) < hi*hi)
        if HAVE_FLINT:
            ball = arb(root['arb_ball'])
            self.assertTrue(ball.overlaps(arb(2)**(arb(-3)/2)))

    def test_face_only_true_by_sturm(self):
        # Bernstein coefficients 3/10,-1/5,3/10 are mixed, yet x^2-x+3/10 has no real root.
        eqs = [[(2, 0, 1), (1, 0, -1), (0, 0, Q(3, 10))], [(0, 1, 1), (1, 0, -1)]]
        self.assertFalse(B.solve_affine_faces(eqs, BOX)['complete'])
        p = MR.refine(eqs, BOX)
        self.assertTrue(p['face_only_property'])
        self.assertFalse(p['face_only_certified_false'])
        self.assertEqual(p['models'], [])
        self.assertTrue(MR.verify(p))

    def test_tampering(self):
        p = MR.refine([[(0, 3, 1), (5, 0, -1)], [(0, 1, 2), (1, 0, -1)]], BOX)
        for mutate in [lambda q: q.__setitem__('models', [[1, 1]]),
                       lambda q: q['interior_roots'][0].__setitem__('isolating_interval', ['0', '1/10']),
                       lambda q: q.__setitem__('face_only_certified_false', False),
                       lambda q: q.__setitem__('remainder', [[3, 0, '1']])]:
            q = copy.deepcopy(p)
            mutate(q)
            self.assertFalse(MR.verify(q))


@unittest.skipUnless(HAVE_FLINT, 'python-flint required')
class LegendreConnectionTests(unittest.TestCase):
    def test_family_partial_fractions(self):
        from perfectpower.curve_families import CurveFamily
        S = L.from_family(CurveFamily({'coefficients': [[0], [0, 1], [-1, -1], [1]]}))
        self.assertEqual(S.poles, [0, 1])
        self.assertEqual(S.residues, [L.LEGENDRE_R0, L.LEGENDRE_R1])
        self.assertEqual(S.residue_at_infinity(), [[Q(1, 2), 0], [Q(1, 2), Q(-1, 2)]])

    def test_frobenius_exact_replay(self):
        charts = L.legendre_charts(30)
        self.assertEqual(charts['0']['kind'], 'nilpotent_log')
        self.assertEqual(charts['1']['kind'], 'nilpotent_log')
        inf = charts['infinity']
        self.assertEqual(inf['kind'], 'positive_resonance')
        self.assertEqual(inf['resonance_order'], 1)
        self.assertEqual(inf['log_coefficient'], Q(-1, 2))
        for chart in charts.values():
            R, F, sg = chart['R'], chart['F'], chart['sigma']
            for sol in chart['solutions']:
                rho, ys, zs = sol['rho'], sol['y'], sol['z']
                for n in range(len(ys)):
                    yp = ys[n-1] if n else [0, 0]
                    zp = zs[n-1] if n else [0, 0]
                    # (1-sg s) s Y' = (R + F s) Y, coefficient of s^(n+rho), log^1 and log^0
                    for i in range(2):
                        log1 = (n+rho)*zs[n][i]-sg*(n-1+rho)*zp[i]-sum(R[i][j]*zs[n][j]+F[i][j]*zp[j] for j in range(2))
                        log0 = ((n+rho)*ys[n][i]+zs[n][i]-sg*(n-1+rho)*yp[i]-sg*zp[i]
                                - sum(R[i][j]*ys[n][j]+F[i][j]*yp[j] for j in range(2)))
                        self.assertEqual((log1, log0), (0, 0))

    def test_resonance_needs_log(self):
        inf = L.legendre_charts(4)['infinity']
        b, u, v = inf['resonance_rhs'], inf['eigenvector_lo'], inf['eigenvector_hi']
        # b is not in the range span(u) of (1/2-R): a log-free exponent -1/2 solution is impossible
        self.assertNotEqual(u[0]*b[1]-u[1]*b[0], 0)

    def test_matches_formal_resonant_jet(self):
        from perfectpower.curve_families import CurveFamily
        fam = CurveFamily({'coefficients': [[0], [0, 1], [-1, -1], [1]]})
        jet = fam.resonant_frobenius('infinity', order=6, exponent='-1/2', seed=[0, 1])
        theirs = [[Q(c['numerator'][0]) for c in jet['coefficients'][n][1]] for n in range(6)]
        mine = L.legendre_charts(6)['infinity']['solutions'][1]['z']
        # same log series up to the seed sign (our seed is (0,-1))
        self.assertEqual(theirs, [[-x for x in v] for v in mine])

    def test_tail_bound_consistency(self):
        old = ctx.prec
        ctx.prec = 192
        try:
            for name in ('0', 'infinity'):
                a, ta = L.frobenius_matrix(L.legendre_charts(40)[name], Q(1, 2))
                b, tb = L.frobenius_matrix(L.legendre_charts(120)[name], Q(1, 2))
                self.assertTrue(all(a[i, j].overlaps(b[i, j]) for i in range(2) for j in range(2)))
                self.assertLess(max(tb), max(ta))
        finally:
            ctx.prec = old

    def test_monodromy_packet(self):
        p = L.legendre_packet(prec=128, order=70, target_bits=90)
        m = p['monodromy']
        self.assertEqual(m['N0'], [[1, 2], [0, 1]])
        self.assertEqual(m['N1'], [[1, 0], [-2, 1]])
        self.assertEqual(m['Ninf_outer'], m['relations']['N1*N0'])
        self.assertTrue(m['frobenius_agree'])
        self.assertTrue(all(m['gamma2'].values()))
        self.assertTrue(p['period_determinant_closed_form']['consistent'])
        self.assertTrue(all(v['closed_form_period_coordinates']['balls_overlap'] for v in p['frobenius_certificates'].values()))
        self.assertTrue(p['positive_resonance']['log_term_necessary'])
        self.assertEqual(p, L.legendre_packet(prec=128, order=70, target_bits=90))

    def test_certified_transport_matches_numeric(self):
        import numpy as np
        from perfectpower.curve_families import CurveFamily
        from perfectpower import family_continuation as FC
        fam = CurveFamily({'coefficients': [[0], [0, 1], [-1, -1], [1]]})
        path = ['1/2', ['0', '1/2'], ['-1/2', '0'], ['0', '-1/2'], '1/2']
        packet, T = L.certified_transport(fam, path)
        self.assertTrue(packet['certified_error_bound'])
        num = FC.transport(fam, path, tolerance=1e-12)['transfer_matrix']
        for i in range(2):
            for j in range(2):
                z = complex(*num[i][j])
                w = T[i, j]
                self.assertLess(abs(complex(float(w.real.mid()), float(w.imag.mid()))-z), 1e-8)

    def test_rejections(self):
        S = L.legendre_system()
        with self.assertRaises(ValueError):
            S.transport(['-1/2', '1/2'])
        with self.assertRaises(ValueError):
            S.taylor_step(Q(1, 2), Q(1, 4), 60)
        self.assertIsNone(L.integer_matrix(acb_mat([[acb(arb(1, 1)), 0], [0, 1]])))
        self.assertEqual(L.integer_matrix(acb_mat([[acb(arb(1, 0.25)), 0], [0, 1]])), [[1, 0], [0, 1]])
        with self.assertRaises(ValueError):
            L.frobenius_matrix(L.legendre_charts(10)['0'], Q(3, 2))


if __name__ == '__main__':
    unittest.main()
