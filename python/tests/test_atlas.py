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


class TestIntegerValued(unittest.TestCase):
    def test_integerize_preserves_hits(self):
        from perfectpower.atlas import integerize
        tri = (0, Fraction(1, 2), Fraction(1, 2))              # n(n+1)/2
        f = integerize(tri, 2)
        self.assertEqual(f, (0, 2, 2))
        self.assertEqual(brute(f, 2, 2000), [1, 8, 49, 288, 1681])   # square triangular numbers
        self.assertEqual(classify(f, 2).kind, 'pell')
        c3 = (0, Fraction(1, 3), Fraction(-1, 2), Fraction(1, 6))   # binomial(n, 3)
        g = integerize(c3, 2)
        self.assertEqual([n for n in brute(g, 2, 3000) if n >= 3], [3, 4, 50])
        for n in range(1, 60):
            v = n * (n - 1) * (n - 2) // 6
            self.assertEqual(n in brute(g, 2, 60), any(m * m == v for m in range(0, 400)))
        with self.assertRaises(ValueError):
            integerize((0, Fraction(1, 2)), 2)                       # n/2 is not integer-valued


class TestShiftSpectrum(unittest.TestCase):
    def test_named(self):
        from perfectpower.atlas import shift_spectrum
        sp = shift_spectrum((0, -3, 0, 1), 2)       # n^3 - 3n + k, critical values k = +-2
        self.assertEqual(sorted(sp['critical_shifts']), [-2, 2])
        self.assertEqual(sp['generic_kind'], 'finite')
        self.assertEqual(sp['critical_shifts'][2]['kind'], 'radical')
        self.assertEqual(shift_spectrum((0, 0, 1), 2)['critical_shifts'][0]['kind'], 'power')
        self.assertEqual(shift_spectrum((0, 1, 1), 2)['critical_shifts'], {})

    def test_generic_type_off_critical_set(self):
        from perfectpower.atlas import shift_spectrum
        rng = random.Random(9)
        for _ in range(120):
            m, d = rng.randrange(1, 5), rng.choice([2, 3, 4])
            S = [rng.randrange(-6, 7) for _ in range(m)] + [rng.choice([1, -1, 2, 3])]
            sp = shift_spectrum(S, d)
            for k in range(-25, 26):
                f = list(S)
                f[0] += k
                _, parts = squarefree_decomposition(normalize(f))
                repeated = any(j > 1 for j in parts)
                self.assertEqual(repeated, k in sp['critical_shifts'], (S, k))
                if not repeated:
                    self.assertEqual(classify(f, d).kind, sp['generic_kind'], (S, d, k))


class TestSchaffer(unittest.TestCase):
    def test_exceptional_pairs(self):
        from perfectpower.atlas import integerize
        from perfectpower.polyalg import interpolate
        infinite = []
        for k in range(1, 9):
            Sk = interpolate(list(range(k + 2)), [sum(i ** k for i in range(1, x + 1)) for x in range(k + 2)])
            for d in range(2, 6):
                if classify(integerize(Sk, d), d).growth != 'bounded':
                    infinite.append((k, d))
        self.assertEqual(infinite, [(1, 2), (3, 2), (3, 4), (5, 2)])
        S5 = interpolate(list(range(7)), [sum(i ** 5 for i in range(1, x + 1)) for x in range(7)])
        f = integerize(S5, 2)
        self.assertEqual(structural_hits(f, 2, 2000), [1, 13, 133, 1321])
        self.assertEqual(structural_hits(f, 2, 2000), brute(f, 2, 2000))

    def test_exact_power_reduction(self):
        # (n+1)^2 with d = 4 reduces to n + 1 = square;  S_3 with d = 6 is not effective
        self.assertEqual(structural_hits([1, 2, 1], 4, 50), [3, 8, 15, 24, 35, 48])
        self.assertEqual(structural_hits([1, 0, 0, 0, 1], 6, 10 ** 6), [])


class TestExponential(unittest.TestCase):
    def test_theorem_E_against_scan(self):
        from perfectpower.core import integer_power_root
        from perfectpower.exponential import exponential_density, exponential_hits
        rng = random.Random(4)
        for _ in range(1500):
            a = rng.randrange(2, 40)
            c = rng.choice([1, -1, 2, -8, 12, 27, -27, 32, 64, 72, 1000, -243, 5, 343])
            d = rng.randrange(2, 9)
            scan = [n for n in range(1, 70) if integer_power_root(c * a ** n, d) is not None]
            self.assertEqual(exponential_hits(c, a, d, 69), scan, (c, a, d))
        self.assertEqual(exponential_density(1, 2, 2), Fraction(1, 2))
        self.assertEqual(exponential_density(1, 36, 4), Fraction(1, 2))
        self.assertEqual(exponential_density(1, 8, 6), Fraction(1, 2))   # 8 = 2^3, gcd(6,3) = 3


class TestSandwichCover(unittest.TestCase):
    def test_cover_is_sound_numerically(self):
        from perfectpower.lean_sandwich import Cover, _eval
        from perfectpower.lean_emit import _ints
        for f, d in (([0, 120, 274, 225, 85, 15, 1], 2), ([1, 1, 1, 1, 1], 2),
                     ([0, 5040, 13068, 13132, 6769, 1960, 322, 28, 1], 4)):
            cov = Cover(f, d)
            pieces, (c, tc) = cov.build()
            P, fi = _ints(cov.P), cov.fi
            covered = []
            for pc in pieces:
                if pc[0] == 'point':
                    covered.append(pc[1])
                    continue
                _, a, b, t = pc
                for n in range(a, b + 1):
                    V = cov.D ** d * _eval(fi, n)
                    p = _eval(P, n) + t
                    self.assertTrue(p >= 0 and p ** d < V < (p + 1) ** d, (f, d, n))
                covered.extend(range(a, b + 1))
            self.assertEqual(covered, list(range(1, c)))
            for n in range(c, c + 500):
                V = cov.D ** d * _eval(fi, n)
                p = _eval(P, n) + tc
                self.assertTrue(p >= 0 and p ** d < V < (p + 1) ** d, (f, d, n))


class TestPellHeat(unittest.TestCase):
    def test_two_term_expansion(self):
        import math
        from perfectpower.atlas import quadratic_square_hits
        from perfectpower.pell_heat import (pell_heat_model, pell_heat_prediction,
                                            pell_heat_prediction_first_order)
        for A, B, C in ((2, 0, 1), (5, 1, 3), (2, 2, 0)):
            classes, ms, msum = pell_heat_model(A, B, C, match=10 ** 6)
            hits = sorted(quadratic_square_hits(A, B, C, 10 ** 30))
            hs = sum(1 for h in hits if h <= 10 ** 6)
            hsum = sum(h for h in hits if h <= 10 ** 6)
            for tau in (1e-6, 1e-9):
                K = math.fsum(math.exp(-tau * h) for h in hits)
                p, _ = pell_heat_prediction(A, B, C, tau, hs, classes, ms)
                self.assertLess(abs(K - p), 20 * tau, (A, B, C, tau))
            for tau in (1e-3, 1e-4, 1e-5):
                K = math.fsum(math.exp(-tau * h) for h in hits)
                q = pell_heat_prediction_first_order(A, B, tau, hs, hsum, classes, ms, msum)
                self.assertLess(abs(K - q), 50 * tau ** 2, (A, B, C, tau))


class TestPellKappaLeanDefinition(unittest.TestCase):
    def test_canonical_kappa_matches_atlas(self):
        # kappa as defined in the Lean theorem PellExact.pell_exact_count (canonical roots,
        # periods mod 2A, good residues) agrees with the atlas constant, including kappa = 0
        from perfectpower.arith import pell_fundamental
        from perfectpower.pell_heat import pell_kappa_canonical
        for A, B, C in [(2, 0, 1), (3, 0, 1), (2, 0, -7), (5, 1, 3), (2, 1, 0), (6, 0, -2),
                        (2, 2, 0), (7, 3, -5), (13, 0, 4), (2, 0, 7)]:
            u, v = pell_fundamental(4 * A)
            k, _ = pell_kappa_canonical(A, B, C, u, v)
            self.assertAlmostEqual(k, classify([C, B, A], 2).details['kappa'], places=10)


class TestGeometry(unittest.TestCase):
    def test_euler_characteristic_matches_types(self):
        # Theorem G: finite type  <=>  chi(affine component) = d'(1 - S) < 0  (Siegel)
        rng = random.Random(11)
        for _ in range(1500):
            d = rng.randrange(2, 9)
            f = (Fraction(rng.choice([1, -2, 3, 4, 8, 9])),)
            for _ in range(rng.randrange(1, 5)):
                lin = (normalize([rng.randrange(-5, 6), 1]) if rng.random() < 0.7
                       else normalize([rng.randrange(1, 5), 0, 1]))
                f = mul(f, power(lin, rng.randrange(1, 7)))
            cl = classify([int(x) for x in normalize(f)], d)
            self.assertEqual(cl.curve['siegel_finite'], cl.kind == 'finite', (f, d))

    def test_named_curves(self):
        self.assertEqual(classify([1, 0, 0, 1], 2).curve['genus'], 1)          # y^2 = x^3 + 1
        self.assertEqual(classify([1, 0, 2], 2).curve['points_at_infinity'], 2)  # Pell, genus 0
        self.assertEqual(classify([1, 0, 2], 2).curve['genus'], 0)
        self.assertEqual(classify([1, 1, 1, 1, 1], 2).curve['genus'], 1)      # Ljunggren quartic
        self.assertEqual(classify([0, 0, 0, 0, 0, 1], 3).curve['genus'], 0)   # y^3 = x^5: radical type
        self.assertEqual(classify([2, 0, 0, 0, 0, 1], 3).curve['genus'], 4)   # y^3 = x^5 + 2: (2*4 - 0)/2


class TestFrontier(unittest.TestCase):
    def test_pillai_instances_are_finite_type_except_2_2(self):
        # x^a - y^b = k is the atlas instance F = x^a - k, d = b: x^a - k is squarefree for k != 0,
        # so LeVeque's exceptional patterns occur only in the Pell case a = b = 2.
        for a in range(2, 7):
            for b in range(2, 7):
                for k in (-7, -2, -1, 1, 2, 5, 12):
                    kind = classify([-k] + [0] * (a - 1) + [1], b).kind
                    self.assertEqual(kind, 'pell' if a == b == 2 else 'finite', (a, b, k))

    def test_mordell_curves_are_finite_type(self):
        for k in (-26, -2, 1, 17, 24):
            self.assertEqual(classify([k, 0, 0, 1], 2).kind, 'finite')

    def test_pillai_census_small(self):
        import subprocess, sys, os
        env = dict(os.environ, PYTHONPATH='python')
        out = subprocess.run([sys.executable, 'python/pillai_census.py', '8', '100'],
                             capture_output=True, text=True, env=env, check=True).stdout
        self.assertIn('"pairs": 255', out)            # equals an independent brute force at 1e8
        self.assertIn('"k_equal_1": [[8, 9]]', out)   # Catalan / Mihailescu regression
        subprocess.run([sys.executable, 'python/pillai_census.py', '18', '1000'],
                       capture_output=True, text=True, env=env, check=True)   # restore receipt


class TestLeanEmitter(unittest.TestCase):
    def test_plans_and_hits(self):
        from perfectpower.lean_emit import emit, plan
        pl = plan([1, 1, 1, 1, 1], 2)
        self.assertEqual((pl['x0'], pl['T']), (4, 1))
        text = emit('t', [1, 1, 1, 1, 1], 2)
        self.assertIn("n ∈ ({3} : Finset ℕ)", text)
        self.assertIn('exact ⟨11, by norm_num⟩', text)
        self.assertIsNone(plan([1, 0, 2], 2))          # nonrigid
        self.assertIsNone(plan([0, 0, 1], 2))          # exact power

    def test_shifted_polynomials_are_definite(self):
        from perfectpower.lean_emit import _definite, plan
        for f, d in (([0, 6, 11, 6, 1], 2), ([1, 1, 0, 0, 0, 0, 1], 3), ([7, 0, 0, 0, 1], 2)):
            pl = plan(f, d)
            self.assertEqual(_definite(pl['Ps']), 1)
            for _, sh in pl['conds']:
                self.assertEqual(_definite(sh), 1)
            for t, (_, sh, sgn) in pl['Gs'].items():
                self.assertNotEqual(sgn, 0)


if __name__ == '__main__':
    unittest.main()
