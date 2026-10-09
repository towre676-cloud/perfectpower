import random
import unittest

try:
    import cypari2  # noqa: F401
    HAVE_PARI = True
except ImportError:  # pragma: no cover
    HAVE_PARI = False

if HAVE_PARI:
    from perfectpower import wild_conductors as W
    from perfectpower.dyadic_reduction import tate


def g2exp(P, c, p):
    r = P.genus2red(W._pol(P, c), p)
    fa = r[1]
    for i in range(int(P.matsize(fa)[0])):
        if int(fa[i, 0]) == p:
            return int(fa[i, 1])
    return 0


@unittest.skipUnless(HAVE_PARI, 'cypari2 required')
class PermutationAndIdentityTests(unittest.TestCase):
    def test_gl2f3_identity(self):
        import develop_wild_conductors as D
        r = D.identity_section()
        self.assertEqual(r['failures'], 0)
        self.assertEqual(r['sylow_order'], 16)

    def test_permutation_swan(self):
        P = W.pari()
        self.assertEqual(W.permutation_conductor(P('x^3-2'), 3, P)['swan'], 1)
        self.assertEqual(W.permutation_conductor(P('x^2+1'), 2, P)['swan'], 1)
        self.assertEqual(W.permutation_conductor(P('x^2-3'), 3, P)['swan'], 0)
        self.assertEqual(W.permutation_conductor(P('(x-1)*(x^2-2)'), 2, P)['artin'], 3)


@unittest.skipUnless(HAVE_PARI, 'cypari2 required')
class EllipticTests(unittest.TestCase):
    def test_named(self):
        P = W.pari()
        for a, p, f, sw in (([0, 0, 0, 0, 2], 2, 6, 4), ([0, 0, 0, -1, 0], 2, 5, 3), ([0, 0, 0, 0, 3], 3, 5, 3),
                            ([1, 0, 1, 4, -6], 2, 1, 0), ([0, 0, 0, -1, 1], 2, 2, 0)):
            r = W.elliptic_conductor_galois(a, p, P)
            self.assertEqual((r['conductor_exponent'], r['swan']), (f, sw), (a, p))

    def test_multiplicative_twist(self):
        P = W.pari()
        # 14a1 has multiplicative reduction at 2; its twist by Q(i) is additive there
        self.assertEqual(W.elliptic_tame_part([1, 0, 1, 4, -6], 2, P)['tame'], 1)
        tw = P.ellinit(P.elltwist(P.ellinit([1, 0, 1, 4, -6]), -4))
        a = [int(x) for x in tw[:5]]
        self.assertEqual(W.elliptic_tame_part(a, 2, P)['tame'], 2)

    def test_random_against_elllocalred(self):
        P = W.pari()
        rng = random.Random(5)
        n = 0
        while n < 25:
            a = [rng.randint(-1, 1), rng.randint(-3, 3), rng.randint(-1, 1), rng.randint(-20, 20), rng.randint(-30, 30)]
            E = P.ellinit(a)
            if len(E) == 0 or E[11] == 0:
                continue
            for p in (2, 3):
                fp = int(P.elllocalred(E, p)[0])
                if fp == 0:
                    continue
                n += 1
                r = W.elliptic_conductor_galois(a, p, P)
                self.assertEqual(r['conductor_exponent'], fp, (a, p))
                self.assertEqual(r['swan'], tate(a, p)['swan'])

    def test_filtration_replay(self):
        P = W.pari()
        r = W.elliptic_conductor_galois([0, 0, 0, 0, 2], 2, P, filtration=True)
        self.assertEqual(r['swan_filtration']['swan'], 4)
        r = W.elliptic_conductor_galois([0, 0, 0, 0, 3], 3, P, filtration=True)
        self.assertEqual(r['swan_filtration']['swan'], 3)

    def test_ogg(self):
        self.assertEqual(W.ogg_exponent('II', 6), 6)
        self.assertEqual(W.ogg_exponent('I3*', 12), 5)
        self.assertEqual(W.kodaira_components('IV*'), 7)
        self.assertEqual(W.pari_kodaira_symbol(-7), 'I3*')


@unittest.skipUnless(HAVE_PARI, 'cypari2 required')
class GenusTwoOddTests(unittest.TestCase):
    def test_wild_and_tame(self):
        P = W.pari()
        from sympy import symbols, Poly
        x = symbols('x')
        polys = [((x ** 3 - 3) * (x ** 3 - 2), 3, 8), (x ** 6 - 3, 3, 10), (x ** 5 - 5, 5, 9),
                 ((x ** 3 + 3 * x + 3) * (x ** 2 - 7) * (x - 1), 3, None), ((x ** 4 - 5) * x, 5, 4),
                 ((x ** 3 - 3) * (x - 1) * (x - 4) * (x - 7), 3, 7)]
        for f, p, expect in polys:
            c = [int(v) for v in reversed(Poly(f, x).all_coeffs())]
            r = W.curve_conductor_galois(c, p, P)
            ref = g2exp(P, c, p)
            self.assertEqual(r['conductor_exponent'], ref, (f, p))
            if expect is not None:
                self.assertEqual(ref, expect)

    def test_multiplicities_matter(self):
        P = W.pari()
        r = W.curve_conductor_galois([-3, 0, 0, 0, 0, 0, 1], 3, P)
        self.assertGreater(r['wild_translations'], 0)
        self.assertNotEqual(r['naive_multiplicity_conductor'], str(r['conductor_exponent']))

    def test_p2_refused(self):
        with self.assertRaises(ValueError):
            W.curve_conductor_galois([1, 0, 0, 0, 0, 1], 2)


@unittest.skipUnless(HAVE_PARI, 'cypari2 required')
class GenusTwoAtTwoTests(unittest.TestCase):
    def test_bielliptic(self):
        P = W.pari()
        self.assertEqual(W.bielliptic_conductor_galois([1, 1, 0, 1], 2, P)['conductor_exponent'], 7)
        # LMFDB 15360.f.983040.2: y^2 = -2x^6-15x^4-37x^2-30, conductor 2^10 * 15
        self.assertEqual(W.bielliptic_conductor_galois([-30, -37, -15, -2], 2, P)['conductor_exponent'], 10)

    def test_functional_equation_oracle(self):
        P = W.pari()
        P.default('realprecision', 38)
        f = [1, 0, 1, 0, 0, 0, 1]
        self.assertLessEqual(W.analytic_exponent_check(f, 961, 7, P), -30)
        self.assertGreater(W.analytic_exponent_check(f, 961, 6, P), -20)
        # Euler factor at 2 must be supplied when an elliptic factor has good reduction at 2
        f = [-2, 0, -4, 0, 0, 0, 4]
        E1, E2 = W.bielliptic_factors([-2, -4, 0, 4])
        F2 = W.poly_mul(W.elliptic_euler_factor_2(W._integral_ainvs(E1), P), W.elliptic_euler_factor_2(W._integral_ainvs(E2), P))
        self.assertEqual(F2, [1, 2, 2])
        self.assertGreater(W.analytic_exponent_check(f, 121, 6, P), -20)
        self.assertLessEqual(W.analytic_exponent_check(f, 121, 6, P, euler2=F2), -30)

    def test_mobius(self):
        P = W.pari()
        f = [1, 0, 1, 0, 0, 0, 1]
        fm = W.mobius_sextic(f, (1, 1, 1, 2))
        self.assertEqual(len(fm), 7)
        self.assertEqual(int(P.genus2red(W._pol(P, f))[0]), int(P.genus2red(W._pol(P, fm))[0]))


if __name__ == '__main__':
    unittest.main()
