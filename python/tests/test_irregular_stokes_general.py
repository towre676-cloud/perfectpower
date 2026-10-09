import unittest
from fractions import Fraction as Q

from perfectpower.irregular_stokes import kummer_system, kummer_closed_forms, formal_normal_form
from perfectpower.irregular_stokes_general import (
    formal_data, asymptotic_bound, best_truncation, certified_stokes, birkhoff2_closed_form, balls_overlap,
    op_from_ode, op_mul, turrittin_scalar, reduce_to_rank_one, exps_record, newton_edges)


def acb_i():
    from flint import acb
    return acb(0, 1)


class FormalTests(unittest.TestCase):
    def test_matches_irregular_stokes_and_replays(self):
        A = [[[0, 1, 0], [0, 1, 1], [0, 0, 3]], [['1/2', 0, 1], [1, '-1/3', 0], [0, 2, '1/5']]]
        fd = formal_data(A, order=20)
        self.assertTrue(fd['identity_checked'])
        self.assertTrue(fd['matches_irregular_stokes'])
        ch = formal_normal_form(A, order=20)
        self.assertEqual(ch['formal_exponents'], [str(x) for x in fd['mu']])

    def test_cluster_normal_form(self):
        fd = formal_data([[[1, 0, 0], [0, 1, 0], [0, 0, 0]], [['1/3', '1/2', 1], ['1/6', 0, '2/3'], ['1/2', 1, '1/7']]], order=25)
        self.assertEqual([str(x) for x in fd['lam']], ['0', '1', '1'])
        self.assertEqual([str(x) for x in fd['mu']], ['1/7', '-1/6', '1/2'])
        # the residue block on the repeated eigenvalue is diagonal in the chosen frame
        self.assertEqual(fd['B'][1][1][2], 0)
        self.assertEqual(fd['B'][1][2][1], 0)

    def test_rejections(self):
        with self.assertRaises(ValueError):  # Jordan leading term: needs Turrittin
            formal_data([[[1, 1], [0, 1]], [[0, 0], [1, 0]]], order=10)
        with self.assertRaises(ValueError):  # resonant residue on a repeated eigenvalue
            formal_data([[[1, 0], [0, 1]], [[0, 0], [0, 1]]], order=10)

    def test_bound_is_exact_and_monotone(self):
        fd = formal_data(kummer_system('1/3', '3/4'), order=60)
        b1 = best_truncation(fd, 16)
        b2 = best_truncation(fd, 32)
        self.assertIsInstance(b1['eta'], Q)
        self.assertLess(b2['eta'], b1['eta'] / 10 ** 5)
        self.assertIsNone(asymptotic_bound(fd, 50, 2))  # radius too small: no admissible bound


class CertifiedTests(unittest.TestCase):
    def test_kummer_contains_closed_forms(self):
        rec, raw = certified_stokes(kummer_system('2/5', '7/3'), 20)
        self.assertTrue(rec['certified'])
        s0, sp = kummer_closed_forms('2/5', '7/3')
        self.assertTrue(raw['S0'][0, 1].overlaps(s0))
        self.assertTrue(raw['S_pi'][1, 0].overlaps(sp))
        for c in birkhoff2_closed_form(raw['fd']):
            self.assertTrue(c['s0'].overlaps(s0) and c['s_pi'].overlaps(sp))

    def test_no_closed_form_two_radii(self):
        A = [[[0, 0], [0, 1]], [['1/3', 1], [1, '-1/2']], [[0, '1/5'], ['2/7', 0]]]
        r1, w1 = certified_stokes(A, 16)
        r2, w2 = certified_stokes(A, 22)
        self.assertTrue(r1['certified'] and r2['certified'])
        self.assertTrue(balls_overlap(w1, w2))
        mid = complex(float(w2['S0'][0, 1].real.mid()), float(w2['S0'][0, 1].imag.mid()))
        self.assertAlmostEqual(mid.imag, 1.77711581377346, places=6)

    def test_three_by_three_local_exponents(self):
        A = [[[-1, 0, 0], [0, 0, 0], [0, 0, 1]], [['1/3', 1, '-1/2'], ['2/5', '-1/4', 1], [1, '1/7', '1/2']]]
        rec, raw = certified_stokes(A, 16)
        self.assertTrue(rec['certified'])
        self.assertTrue(rec['checks']['charpoly_matches_local_exponents_at_0'])
        self.assertEqual(len(rec['stokes_entries']), 6)

    def test_repeated_eigenvalue_block_zero(self):
        from perfectpower.irregular_stokes_general import _fmat, _mul, _inv
        a, b, c = Q(1, 3), Q(3, 4), Q(2, 5)
        G = _fmat([[1, 1, 0], [0, 1, 1], [1, 0, 1]])
        A = [_mul(_mul(G, _fmat(m)), _inv(G)) for m in ([[0, 1, 0], [0, 1, 0], [0, 0, 1]], [[0, 0, 0], [a, -b, 0], [0, 0, c]])]
        rec, raw = certified_stokes(A, 18)
        self.assertTrue(rec['certified'])
        s0, sp = kummer_closed_forms(a, b)
        S0, Sp = raw['S0'], raw['S_pi']
        prods = [S0[0, j] * Sp[j, 0] for j in (1, 2)]
        self.assertEqual(sorted(bool(p.overlaps(s0 * sp)) for p in prods), [False, True])

    def test_negative_control(self):
        A = kummer_system('1/3', '3/4')
        fd = formal_data(A, order=60)
        eta = best_truncation(fd, 18)['eta'] / 1000
        rec, _ = certified_stokes(A, 18, fd=fd, eta_override=eta)
        self.assertFalse(rec['certified'])
        self.assertFalse(rec['checks']['sectorial_enclosures_consistent_along_axis'])


class TurrittinTests(unittest.TestCase):
    def test_newton_polygon_airy(self):
        L = op_from_ode([{1: -1}, {}, {0: 1}])
        ed = [e for e in newton_edges(L) if e['m'] > 0]
        self.assertEqual([e['m'] for e in ed], [Q(3, 2)])

    def test_exponents(self):
        rec = exps_record(turrittin_scalar(op_from_ode([{1: -1}, {}, {0: 1}])))
        self.assertEqual(sorted((tuple(e['exponential'].items()), e['z_power']) for e in rec),
                         [((('3/2', '-2/3'),), '-1/4'), ((('3/2', '2/3'),), '-1/4')])
        rec = exps_record(turrittin_scalar(op_from_ode([{1: 1, 0: -2}, {0: 1, 1: -2}, {1: 1}])))
        self.assertEqual(sorted(e['exponential']['1/2'] for e in rec), ['-2', '2'])
        self.assertTrue(all(e['exponential']['1'] == '1' and e['z_power'] == '-1/4' for e in rec))
        rec = exps_record(turrittin_scalar(op_from_ode([{1: -1}, {}, {}, {0: 1}])))
        self.assertEqual(len(rec), 3)
        self.assertTrue(all(e['z_power'] == '-1/3' and e['q'] == 3 for e in rec))
        from sympy import Rational
        L = op_mul({(Q(0), 1): Rational(1), (Q(1), 0): Rational(-1)}, {(Q(0), 2): Rational(1), (Q(1), 0): Rational(-1)})
        rec = exps_record(turrittin_scalar(L))
        self.assertIn({'1': '1'}, [e['exponential'] for e in rec])

    def test_airy_certified(self):
        red = reduce_to_rank_one(op_from_ode([{1: -1}, {}, {0: 1}]))
        self.assertEqual((red['q'], red['p']), (2, 3))
        rec, raw = certified_stokes(red['A'], 16)
        self.assertTrue(rec['certified'])
        self.assertTrue(raw['S0'][0, 1].overlaps(acb_i()))
        self.assertTrue(raw['S_pi'][1, 0].overlaps(-acb_i()))
        self.assertLess(rec['max_ball_radius'], 1e-6)

    def test_repeated_jordan_bessel(self):
        red = reduce_to_rank_one(op_from_ode([{1: 1, 0: Q(-7, 3)}, {0: Q(4, 3), 1: -2}, {1: 1}]))  # nu=1/3
        self.assertEqual(red['psi'], {'1': '1'})
        rec, raw = certified_stokes(red['A'], 10)
        self.assertTrue(rec['certified'])
        self.assertTrue(raw['S0'][0, 1].overlaps(acb_i()))  # 2i cos(pi/3)

    def test_weber_classical(self):
        from flint import acb, arb, fmpq
        red = reduce_to_rank_one(op_from_ode([{2: Q(-1, 4), 0: Q(-1, 3)}, {}, {0: 1}]))
        rec, raw = certified_stokes(red['A'], 48)
        self.assertTrue(rec['certified'])
        s0 = acb_i() * (2 * acb.pi()).sqrt() * (acb(1) / 2 - acb(arb(fmpq(1, 3)))).rgamma()
        self.assertTrue(raw['S0'][0, 1].overlaps(s0))

    def test_not_quasi_homogeneous(self):
        with self.assertRaises(ValueError):  # w''=(z+1/z)w: t^-2 term breaks the s=t^3 reduction
            reduce_to_rank_one(op_from_ode([{1: -1, -1: -1}, {}, {0: 1}]))


if __name__ == '__main__':
    unittest.main()
