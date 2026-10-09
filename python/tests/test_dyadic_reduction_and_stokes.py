import random
import unittest
from fractions import Fraction as Q

from perfectpower.tame_cluster_frobenius import (root_galois_data, analyse_curve, extension_tamagawa,
                                                 swan_conductor_roots, TameField)
from perfectpower.semistable_tamagawa import rational_root_tamagawa
from perfectpower.dyadic_reduction import (tate, kodaira_pari_code, genus_one_reduction, genus2_good_reduction_certificate,
                                           good_model_genus2_at_2, bielliptic_reduction)
from perfectpower.irregular_stokes import (formal_normal_form, kummer_system, certified_kummer_stokes, late_term_stokes,
                                           kummer_closed_forms, borel_pade_stokes)

try:
    import cypari2
    PARI = cypari2.Pari()
except ImportError:  # pragma: no cover
    PARI = None


def pol(c):
    return PARI('Pol([%s])' % ','.join(str(x) for x in reversed(c)))


def g2exp(c, p):
    r = PARI.genus2red(pol(c), p)
    fa = r[1]
    for i in range(int(PARI.matsize(fa)[0])):
        if int(fa[i, 0]) == p:
            return int(fa[i, 1])
    return 0


def expand(*factors, lead=1):
    from sympy import symbols, Poly, prod
    x = symbols('x')
    f = Poly(lead * prod(eval(s, {'x': x}) for s in factors), x)
    return [int(c) for c in reversed(f.all_coeffs())]


class TameFieldTests(unittest.TestCase):
    def test_valuation_and_inverse(self):
        L = TameField(5, 2, 4, 20)
        x = L.add(L.from_zeta_poly([3, 1]), L.varpi_power(3))
        self.assertEqual(L.v(x), 0)
        y = L.mul(x, L.inverse(x))
        self.assertGreaterEqual(L.v(L.sub(y, L.one)), 20)
        self.assertEqual(L.v(L.varpi_power(-7)), Q(-7, 4))

    def test_galois_on_roots(self):
        d = root_galois_data([-2, 0, 1], 3)
        self.assertEqual((d['field'].f, d['field'].e), (2, 1))
        self.assertEqual(d['frobenius'], [1, 0])
        self.assertEqual(d['inertia'], [0, 1])
        d = root_galois_data([-3, 0, 1], 3)
        self.assertEqual((d['field'].f, d['field'].e), (1, 2))
        self.assertEqual(d['inertia'], [1, 0])
        d = root_galois_data([-7, 0, 0, 1], 7)
        self.assertEqual(d['field'].e, 3)
        self.assertEqual(sorted(len(set(_orbit(d['inertia'], i))) for i in range(3)), [3, 3, 3])

    def test_rejections(self):
        with self.assertRaises(ValueError):
            analyse_curve([1, 0, 0, 1], 2)
        with self.assertRaises(ArithmeticError):
            root_galois_data([-3, 0, 0, 1], 3)  # wild: x^3=3 over Q_3
        with self.assertRaises(ValueError):
            extension_tamagawa(expand('x**3-7', 'x**3-2'), 7)  # e=3: not semistable
        with self.assertRaises(ValueError):
            TameField(3, 1, 3)


def _orbit(perm, i):
    out, x = [], i
    while x not in out:
        out.append(x)
        x = perm[x]
    return out


@unittest.skipIf(PARI is None, 'cypari2 required')
class ExtensionTamagawaTests(unittest.TestCase):
    def test_conjugate_twin_over_unramified_quadratic(self):
        # Type I2: c_p=2 whether split or not, so the split/nonsplit distinction is
        # tested through the Frobenius sheet sign against PARI's a_p=+-1.
        for lead, split in [(1, False), (2, True)]:
            c = expand('x**2-18', 'x-1', lead=lead)
            t = extension_tamagawa(c, 3)
            E = PARI.ellinit(PARI.ellfromeqn(PARI('y^2-(%s)' % pol(c))))
            lr = PARI.elllocalred(E, 3)
            self.assertEqual(t['splitting_field']['f'], 2)
            self.assertEqual(t['tamagawa_number'], int(lr[3]))
            self.assertEqual(t['conductor_exponent'], int(lr[0]))
            ap = int(PARI.ellap(PARI.ellinit(PARI.ellminimalmodel(E)), 3))
            self.assertEqual(t['frobenius_sheet_signs']['1'], 1 if split else -1)
            self.assertEqual(ap, 1 if split else -1)

    def test_frobenius_two_cycle_of_twins(self):
        for lead in (1, 2):
            c = expand('((x-1)**2-7)**2-8*(x-1)**2', 'x', 'x+1', lead=lead)
            t = extension_tamagawa(c, 3)
            self.assertIn(2, [len(set(_orbit(t['frobenius_cluster_permutation'], i))) for i in range(len(t['clusters']))])
            grp = sorted(int(x) for x in PARI.genus2red(pol(c), 3)[3][2][1] if int(x) > 1)
            self.assertEqual(t['component_group']['invariant_factors'], grp)
            self.assertLessEqual(t['tamagawa_number'], t['geometric_component_order'])

    def test_random_genus_one_against_elllocalred(self):
        rng = random.Random(5)
        checked = 0
        for _ in range(120):
            p = rng.choice([3, 5, 7])
            c = [rng.randint(-20, 20) for _ in range(rng.choice([3, 4]))] + [rng.choice([1, 2, 3])]
            for k in range(len(c) - 1):
                if rng.random() < 0.5:
                    c[k] *= p ** rng.randint(1, 3)
            if PARI.poldisc(pol(c)) == 0:
                continue
            try:
                t = extension_tamagawa(c, p)
            except (ValueError, ArithmeticError):
                continue
            lr = PARI.elllocalred(PARI.ellinit(PARI.ellfromeqn(PARI('y^2-(%s)' % pol(c)))), p)
            self.assertEqual((t['conductor_exponent'], t['tamagawa_number']), (int(lr[0]), int(lr[3])), c)
            checked += 1
        self.assertGreater(checked, 40)

    def test_tame_conductors_beyond_order_two(self):
        for factors, p, e in [(('x**3-7', 'x**3-2'), 7, 3), (('x**4-5', 'x'), 5, 4), (('x**6-7',), 7, 6)]:
            c = expand(*factors)
            a, _, _ = analyse_curve(c, p)
            self.assertEqual(a['splitting_field']['e'], e)
            self.assertIsNone(a['order_two_replay'])
            self.assertEqual(a['conductor_exponent'], g2exp(c, p))

    def test_rational_root_regression(self):
        for p in (3, 5):
            for d in (1, 2):
                for lead in (1, 2):
                    old = rational_root_tamagawa(p, [0, p ** d, 1], lead)
                    new = extension_tamagawa(expand('x', 'x-%d' % p ** d, 'x-1', lead=lead), p)
                    self.assertEqual(old['tamagawa_number'], new['tamagawa_number'])

    def test_swan_against_tate_at_three(self):
        rng = random.Random(8)
        for _ in range(25):
            c = [rng.randint(-9, 9) * 3 ** rng.randint(0, 2) for _ in range(3)] + [1]
            if PARI.poldisc(pol(c)) == 0:
                continue
            self.assertEqual(swan_conductor_roots(c, 3, PARI)['swan'], genus_one_reduction(c, 3)['swan'])


@unittest.skipIf(PARI is None, 'cypari2 required')
class DyadicTests(unittest.TestCase):
    def test_tate_against_elllocalred(self):
        rng = random.Random(3)
        for _ in range(400):
            a = [rng.randint(-3, 3) * rng.choice([1, 2, 4, 8, 3, 9]) for _ in range(5)]
            E = PARI.ellinit(a)
            if len(E) == 0:
                continue
            for p in (2, 3, 7):
                m = tate(a, p)
                lr = PARI.elllocalred(E, p)
                self.assertEqual((m['conductor_exponent'], kodaira_pari_code(m['kodaira']), m['tamagawa']),
                                 (int(lr[0]), int(lr[1]), int(lr[3])), (a, p))

    def test_known_curves(self):
        self.assertEqual(tate([0, -1, 1, -10, -20], 11)['kodaira'], 'I5')
        m = tate([0, 0, 0, -1, 0], 2)
        self.assertEqual((m['conductor_exponent'], m['swan']), (5, 3))
        m = tate([0, 0, 0, 0, 2], 2)
        self.assertEqual(m['conductor_exponent'], 6)

    def test_quartic_jacobian(self):
        rng = random.Random(4)
        for _ in range(60):
            c = [rng.randint(-9, 9) for _ in range(4)] + [rng.choice([1, 2, -3])]
            if PARI.poldisc(pol(c)) == 0:
                continue
            E = PARI.ellinit(PARI.ellfromeqn(PARI('y^2-(%s)' % pol(c))))
            for p in (2, 3):
                m = genus_one_reduction(c, p)
                lr = PARI.elllocalred(E, p)
                self.assertEqual((m['conductor_exponent'], m['tamagawa']), (int(lr[0]), int(lr[3])))

    def test_good_reduction_certificates(self):
        for f in ([1, 0, 0, 0, 0, 4], [1, 4, 4, 2, 0, 0, 1]):
            self.assertIsNotNone(genus2_good_reduction_certificate(f))
            self.assertEqual(g2exp(f, 2), 0)
        self.assertIsNone(genus2_good_reduction_certificate([1, 0, 0, 0, 0, 1]))
        self.assertNotEqual(g2exp([1, 0, 0, 0, 0, 1], 2), 0)
        self.assertFalse(good_model_genus2_at_2([0, 1], [0, 0, 0, 0, 0, 1]))  # y^2+xy=x^5 singular at the origin
        self.assertTrue(good_model_genus2_at_2([1], [0, 0, 0, 0, 0, 1]))

    def test_bielliptic(self):
        rng = random.Random(6)
        for _ in range(40):
            g = [rng.randint(-9, 9) for _ in range(3)] + [1]
            if g[0] == 0:
                continue
            f = [g[0], 0, g[1], 0, g[2], 0, g[3]]
            if PARI.poldisc(pol(f)) == 0:
                continue
            self.assertEqual(bielliptic_reduction(g, 3)['conductor_exponent'], g2exp(f, 3))
            b2 = bielliptic_reduction(g, 2)
            self.assertEqual(b2['conductor_exponent'] == 0, g2exp(f, 2) == 0)
            self.assertGreaterEqual(b2['swan'], 0)


class StokesTests(unittest.TestCase):
    def test_formal_normal_form_kummer(self):
        from sympy import Rational, rf, factorial
        a, b = Rational(1, 3), Rational(3, 4)
        ch = formal_normal_form(kummer_system('1/3', '3/4'), order=30)
        self.assertEqual(ch['formal_exponents'], ['-1/3', '-5/12'])
        F = ch['coefficients']
        for k in range(30):
            self.assertEqual(Rational(F[k][0][0]) + Rational(F[k][1][0]), rf(a, k) * rf(1 + a - b, k) * (-1) ** k / factorial(k))
            self.assertEqual(Rational(F[k][0][1]) + Rational(F[k][1][1]), rf(b - a, k) * rf(1 - a, k) / factorial(k))

    def test_formal_rank_three_and_rejection(self):
        ch = formal_normal_form([[[0, 1, 0], [0, 1, 1], [0, 0, 3]], [['1/2', 0, 1], [1, '-1/3', 0], [0, 2, '1/5']]], order=20)
        self.assertTrue(ch['identity_checked'])
        with self.assertRaises(ValueError):
            formal_normal_form([[[1, 0], [0, 1]], [[0, 1], [0, 0]]])

    def test_certified_airy_and_bessel(self):
        from flint import acb
        out, raw = certified_kummer_stokes('5/6', '5/3')  # Bessel nu=1/3, i.e. Airy
        self.assertTrue(out['certified'])
        self.assertTrue(raw['S0'][0, 1].overlaps(acb(0, 1)))
        out, raw = certified_kummer_stokes('1/2', '1')  # Bessel nu=0, integer b
        self.assertTrue(out['certified'])
        self.assertTrue(raw['S0'][0, 1].overlaps(acb(0, 2)))
        self.assertLess(out['s0_radius'], 1e-25)

    def test_numerical_routes(self):
        import mpmath as mp
        ch = formal_normal_form(kummer_system('2/5', '7/3'), order=60)
        s0, sp = kummer_closed_forms('2/5', '7/3')
        s0 = mp.mpc(float(s0.real.mid()), float(s0.imag.mid()))
        sp = mp.mpc(float(sp.real.mid()), float(sp.imag.mid()))
        lt = late_term_stokes(ch)
        self.assertLess(abs(lt['s0'] - s0), 1e-10)
        self.assertLess(abs(lt['s_pi'] - sp), 1e-10)
        bp = borel_pade_stokes(ch, R=6, dps=30)
        self.assertLess(abs(bp['s0'] - s0), 1e-10)


if __name__ == '__main__':
    unittest.main()
