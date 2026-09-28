import random
import unittest
from fractions import Fraction
from math import gcd, lcm, log

from perfectpower.arith import (factorint, generalized_pell_classes_bruteforce, generalized_pell_solutions,
                                is_square, pell_fundamental, sqrt_mod)
import perfectpower.arith as arith
from perfectpower.atlas import classify, structural_count, structural_hits
from perfectpower.core import floor_nth_root, hit_indices, mul, normalize, power, rigid_certificate
from perfectpower.polyalg import expand_decomposition, integer_roots, squarefree_decomposition
from perfectpower.runge import runge_enumerate


def product(*factors):
    out = (Fraction(1),)
    for f in factors:
        out = mul(out, normalize(f))
    return out


def integral(p):
    D = lcm(*(x.denominator for x in p))
    return [int(x * D) for x in p]


def brute(f, d, N):
    return [n for n, _ in hit_indices(f, d, 0, N)]


class TestPolynomialAlgebra(unittest.TestCase):
    def test_squarefree_and_integer_roots(self):
        rng = random.Random(1)
        for _ in range(200):
            roots = [rng.randrange(-30, 31) for _ in range(rng.randrange(0, 5))]
            p = normalize([rng.choice([1, -2, 3])])
            for r in roots:
                p = mul(p, (Fraction(-r), Fraction(1)))
            p = mul(p, (Fraction(rng.randrange(1, 5)), Fraction(0), Fraction(1)))
            p = mul(p, (Fraction(1), Fraction(3)))
            self.assertEqual(integer_roots(p), sorted(set(roots)))
            c, parts = squarefree_decomposition(p)
            self.assertEqual(expand_decomposition(c, parts), p)

    def test_root_window(self):
        p = product((-5, 1), (-7, 1), (100, 1))
        self.assertEqual(integer_roots(p, lo=6), [7])
        self.assertEqual(integer_roots(p, lo=-100, hi=5), [-100, 5])


class TestArithmetic(unittest.TestCase):
    def test_factor_and_sqrt_mod(self):
        self.assertEqual(factorint(600851475143), {71: 1, 839: 1, 1471: 1, 6857: 1})
        self.assertEqual(factorint(-2 ** 10 * 3 ** 5), {2: 10, 3: 5})
        rng = random.Random(2)
        for _ in range(800):
            m, a = rng.randrange(1, 2000), rng.randrange(-3000, 3000)
            self.assertEqual(sqrt_mod(a, m), [z for z in range(m) if (z * z - a) % m == 0])

    def test_pell(self):
        self.assertEqual(pell_fundamental(2), (3, 2))
        self.assertEqual(pell_fundamental(61), (1766319049, 226153980))
        for D in (2, 3, 5, 6, 7, 8, 12, 13, 28):
            for M in (1, -1, 2, -2, 4, -4, 7, -7, 9, 17, -23, 49, 100):
                X = 3000
                ref = set()
                for x in range(-X, X + 1):
                    v = x * x - M
                    if v % D == 0 and is_square(v // D):
                        y = int((v // D) ** 0.5 + 0.5)
                        while y * y > v // D:
                            y -= 1
                        while (y + 1) ** 2 <= v // D:
                            y += 1
                        ref |= {(x, y), (x, -y)}
                self.assertEqual(generalized_pell_solutions(D, M, X), ref, (D, M))

    def test_lmm_agrees_with_nagell_search(self):
        for D in (2, 3, 5, 7, 10, 13, 17, 20, 44):
            for M in (1, -1, 3, -3, 8, 12, 45, -50, 72, -121, 300):
                X = 10 ** 6
                fast = generalized_pell_solutions(D, M, X)
                saved = arith.generalized_pell_classes
                arith.generalized_pell_classes = generalized_pell_classes_bruteforce
                try:
                    slow = generalized_pell_solutions(D, M, X)
                finally:
                    arith.generalized_pell_classes = saved
                self.assertEqual(fast, slow, (D, M))


class TestRungeEnumeration(unittest.TestCase):
    def test_complete_against_scan(self):
        rng = random.Random(7)
        checked = 0
        for d in (2, 3, 4, 5):
            for _ in range(40):
                q = rng.randrange(1, 3)
                b = rng.choice((-2, -1, 1, 2, 3))
                if rng.random() < 0.4:
                    g = [rng.randrange(-5, 6) for _ in range(q)] + [b]
                    f = [int(x) for x in power(normalize(g), d)]
                    f[0] += rng.randrange(-30, 31)
                else:
                    f = [rng.randrange(-40, 41) for _ in range(d * q)] + [b ** d]
                e = runge_enumerate(f, d)
                if e.exact_identity:
                    continue
                cert = rigid_certificate(f, d)
                limit = min(cert.cutoff + 50, 4000)
                self.assertEqual([n for n, _ in e.hits if n <= limit], brute(f, d, limit), (f, d))
                if cert.cutoff + 50 <= 4000:
                    self.assertTrue(all(n <= limit for n, _ in e.hits))
                    checked += 1
        self.assertGreater(checked, 20)

    def test_named_examples(self):
        self.assertEqual(runge_enumerate([1, 0, 0, 0, 1], 2).hits, [])
        self.assertEqual([n for n, _ in runge_enumerate([0, 1, 1], 2).hits], [])
        self.assertEqual([n for n, _ in runge_enumerate([-24, -39, -34, 30, -22, 10, -29, 33, 1], 4).hits], [])
        self.assertIsNone(runge_enumerate([1, 0, 2], 2))


class TestAtlas(unittest.TestCase):
    def test_structural_hits_match_scan(self):
        rng = random.Random(3)
        seen = set()
        N = 1500
        for _ in range(500):
            d = rng.choice([2, 2, 3, 4, 4, 6])
            mode = rng.randrange(4)
            c = rng.choice([1, -1, 2, 3, -3, 4, 5, 8, 9, 12, 16, 27, -8])

            def lin():
                return (Fraction(rng.randrange(-9, 10)), Fraction(rng.choice([1, 1, 2, 3])))
            if mode == 0:
                r = rng.randrange(1, 2 * d)
                g = [rng.randrange(-3, 4), 1] if rng.random() < 0.5 else [1]
                f = product([c], power(normalize(lin()), r), power(normalize(g), d))
            elif mode == 1:
                if d % 2:
                    d = 2
                e = d // 2
                W = ([rng.randrange(-9, 10), rng.randrange(-5, 6), 1] if rng.random() < 0.6
                     else integral(product(lin(), lin())))
                f = product([c], power(normalize(W), e * rng.choice([1, 1, 3])))
            elif mode == 2:
                g = [rng.randrange(-3, 4), rng.randrange(-3, 4), 1]
                f = product([c], power(normalize(g), d))
            else:
                f = [rng.randrange(-20, 21) for _ in range(rng.randrange(2, 6))] + [c]
            f = integral(normalize(f))
            if len(f) > 9 or max(abs(x) for x in f) > 10 ** 12:
                continue
            cl = classify(f, d)
            try:
                got = structural_hits(f, d, N)
            except NotImplementedError:
                continue
            seen.add(cl.kind)
            self.assertEqual(got, brute(f, d, N), (f, d, cl.kind))
            self.assertEqual(structural_count(f, d, N), len(got), (f, d))
        self.assertEqual(seen, {'power', 'radical', 'pell', 'finite'})

    def test_exponent_spectrum_examples(self):
        # monomials n^r realise every exponent 1/t with t | d
        for d in (2, 3, 4, 6, 12):
            for r in range(1, 2 * d + 1):
                cl = classify([0] * r + [1], d)
                t = d // gcd(r, d)
                self.assertEqual(cl.exponent, Fraction(1, t))
                self.assertEqual(structural_count([0] * r + [1], d, 10 ** 12),
                                 10 ** 12 if t == 1 else floor_nth_root(10 ** 12, t))

    def test_radical_constant(self):
        for f, d, kappa in [((1, 4), 2, 1.0), ((0, 0, 0, 1), 2, 1.0), ((-5, 2), 2, 2 ** -0.5)]:
            cl = classify(f, d)
            self.assertEqual(cl.kind, 'radical')
            self.assertAlmostEqual(cl.details['kappa'], kappa, places=12)
            N = 10 ** 30
            self.assertLessEqual(abs(structural_count(f, d, N) - kappa * N ** 0.5), 10 ** 3)

    def test_pell_constant(self):
        cl = classify((1, 0, 2), 2)
        self.assertEqual(cl.kind, 'pell')
        self.assertAlmostEqual(cl.details['kappa'], 1 / log(3 + 2 * 2 ** 0.5), places=12)
        for N, A in ((10 ** 6, 8), (10 ** 12, 16), (10 ** 24, 31), (10 ** 48, 63)):
            self.assertEqual(structural_count((1, 0, 2), 2, N), A)

    def test_local_global_example(self):
        # Grunwald-Wang: 16 n^8 is an 8th power modulo every odd prime, yet never an 8th power.
        cl = classify((0,) * 8 + (16,), 8)
        self.assertEqual((cl.kind, cl.infinite), ('power', False))
        self.assertEqual(structural_hits((0,) * 8 + (16,), 8, 10 ** 9), [])
        from math import gcd
        for p in (3, 5, 7, 11, 13, 17, 97, 257, 65537):
            g = gcd(8, p - 1)
            self.assertEqual(pow(16, (p - 1) // g, p), 1)

    def test_classification_labels(self):
        cases = {
            ((0, 0, 1), 2): 'power',            # n^2
            ((0, 0, 2), 2): 'power',            # 2 n^2: twisted power, no hits
            ((1, 4), 2): 'radical',             # 4n + 1
            ((1, 0, 2), 2): 'pell',             # 2n^2 + 1
            ((1, 0, 0, 1), 2): 'finite',        # elliptic n^3 + 1
            ((1, 0, 0, 0, 1), 2): 'finite',     # rigid quartic
            ((5,), 2): 'constant',
        }
        for (f, d), kind in cases.items():
            self.assertEqual(classify(f, d).kind, kind, (f, d))


if __name__ == '__main__':
    unittest.main()
