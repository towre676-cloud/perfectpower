"""Constraint compiler and program specialization (perfectpower.compiler, perfectpower.specialize).

Every plan is checked against the definition by direct evaluation.  The cases target the ways a
reduction can go wrong: a square discriminant whose root is not integral, the sign of the square
root, the domain of the recovered variable, zero and negative values, and finite plans that must
not pose as complete lists.
"""
import math
import random
import re
import unittest
from pathlib import Path

from perfectpower.compiler import (padd, ppow, pscale, BOUNDED_EVIDENCE, COMPLETE_FINITE, NOT_ENUMERATED,
                                   STRUCTURED_FILTERED, STRUCTURED_INFINITE, NotEnumerable,
                                   PowerConstraint, QuadraticRootConstraint, TriangularConstraint,
                                   compile_constraint, match_affine_cube, mordell_complete)
from perfectpower.specialize import LoopProgram, parse_poly, specialize

ROOT = Path(__file__).resolve().parents[2]


def brute(con, N):
    return [(n, w) for n in range(1, N + 1) if (w := con.witnesses(n))]


class Reductions(unittest.TestCase):
    def test_square_discriminant_is_not_enough(self):
        # 2y^2 + y = 1: the discriminant 9 is a square, but y = (3 - 1)/4 is not an integer and
        # y = (-3 - 1)/4 = -1 is negative
        con = QuadraticRootConstraint(2, 1, 0, (1,), 'nonneg')
        p = compile_constraint(con)
        self.assertEqual(p.contains(1), [])
        self.assertEqual(p.reduced.witnesses(1), [-3, 3])
        self.assertEqual(compile_constraint(QuadraticRootConstraint(2, 1, 0, (1,), 'int')).contains(1), [-1])

    def test_filter_is_decided(self):
        # 2y^2 + y = n, y >= 0: 8n + 1 = m^2 filtered by 4 | m - 1; decided by periodicity of m
        p = compile_constraint(QuadraticRootConstraint(2, 1, 0, (0, 1), 'nonneg'))
        self.assertFalse(p.chain[0].filter_trivial)
        self.assertEqual(p.status, STRUCTURED_INFINITE)
        self.assertEqual(p.data['filter_decision']['kind'], 'filtered_radical')
        self.assertEqual(list(p.iter_hits(60)), [(3, [1]), (10, [2]), (21, [3]), (36, [4]), (55, [5])])

    def test_filtered_pell_infinite_and_kappa(self):
        # 2y^2 - 4y = 7n^2 - n + 4 (found by the seeded catalogue): the filter keeps some cycles
        con = QuadraticRootConstraint(2, -4, 0, (4, -1, 7), 'int')
        p = compile_constraint(con)
        fd = p.data['filter_decision']
        self.assertEqual(fd['kind'], 'filtered_pell')
        if p.status == STRUCTURED_INFINITE:
            X, Y = fd['witness']
            self.assertGreater(X, 0)
            self.assertGreaterEqual(Y, 0)
            N = 10 ** 30
            self.assertLess(abs(p.count(N) - fd['kappa'] * math.log(N)), 6)
        self.assertEqual(list(p.iter_hits(2000)), brute(con, 2000))

    def test_filtered_pell_finite_has_lean_certificate(self):
        import json
        rows = json.loads((ROOT / 'receipts' / 'plan_certificates.json').read_text())
        finite = [r for r in rows if 'filtered_finite' in r['theorem']]
        self.assertTrue(finite)
        for r in finite:
            self.assertEqual(r['status'], COMPLETE_FINITE)

    def test_triangular_filter_is_trivial(self):
        # Lean: Reduction.triangular_count_nonneg; square triangular numbers
        p = compile_constraint(TriangularConstraint((0, 0, 1), 'nonneg'))
        self.assertTrue(p.chain[0].filter_trivial)
        self.assertEqual(p.status, STRUCTURED_INFINITE)
        self.assertEqual(list(p.iter_hits(1200)), [(1, [1]), (6, [8]), (35, [49]), (204, [288]), (1189, [1681])])

    def test_positive_domain_rejects_zero(self):
        # F(n) = n - 1 is triangular at n = 1 only through y = 0 or y = -1
        self.assertEqual(compile_constraint(TriangularConstraint((-1, 1), 'pos')).contains(1), [])
        self.assertEqual(compile_constraint(TriangularConstraint((-1, 1), 'nonneg')).contains(1), [0])
        self.assertEqual(compile_constraint(TriangularConstraint((-1, 1), 'int')).contains(1), [-1, 0])
        # y >= 1 is a real filter (F = 0 has only y = 0, -1), decided: still infinite
        self.assertEqual(compile_constraint(TriangularConstraint((-1, 1), 'pos')).status, STRUCTURED_INFINITE)

    def test_zero_and_negative_values(self):
        p = compile_constraint(PowerConstraint((-4, 0, 1), 2))       # n^2 - 4: zero at n = 2
        self.assertEqual(p.contains(2), [0])
        cube = compile_constraint(PowerConstraint((-100, 1), 3))    # n - 100 = m^3, m < 0 allowed
        self.assertEqual(cube.contains(92), [-2])
        self.assertEqual(compile_constraint(PowerConstraint((-7, 0, -1), 2)).status, COMPLETE_FINITE)

    def test_affine_transport(self):
        self.assertEqual(match_affine_cube(parse_poly('(5*n - 7)**3 - 2')), (5, -7, -2))
        p = compile_constraint(PowerConstraint(parse_poly('(5*n - 7)**3 - 2'), 2))
        self.assertEqual(p.status, COMPLETE_FINITE)
        self.assertIn('PerfectPower.MordellMinus2.points', p.justification)
        self.assertEqual(p.all_hits(), [(2, [-5, 5])])
        self.assertEqual(p.data['specialized_test'], '5*n + (-7) == 3')
        # the transported argument t = 3 is not of the form 5n + 1 with n >= 1
        self.assertEqual(compile_constraint(PowerConstraint(parse_poly('(5*n + 1)**3 - 2'), 2)).all_hits(), [])
        self.assertEqual(mordell_complete(-432 * 2 ** 6)[0], {48: [288]})

    def test_composite_triangular_cube(self):
        # Lean: Reduction.tri_cube_complete
        p = compile_constraint(TriangularConstraint(parse_poly('64*n**3 - 120*n**2 + 75*n - 16'), 'int'))
        self.assertEqual(p.status, COMPLETE_FINITE)
        self.assertEqual(p.all_hits(), [(1, [-3, 2])])

    def test_pell_far_hit(self):
        p = compile_constraint(PowerConstraint((1, 0, 991), 2))
        self.assertEqual(p.status, STRUCTURED_INFINITE)
        self.assertEqual(list(p.iter_hits(10 ** 27)), [])
        (n, ms), = p.iter_hits(10 ** 29)
        self.assertEqual(n, 12055735790331359447442538767)
        self.assertEqual(991 * n * n + 1, ms[1] ** 2)

    def test_not_enumerated_is_not_empty(self):
        # n^3 + 19: census evidence only; n^3 + 17 is now a theorem
        p = compile_constraint(PowerConstraint(parse_poly('n**3 + 17'), 2))
        self.assertEqual(p.status, COMPLETE_FINITE)
        self.assertEqual([n for n, _ in p.all_hits()], [2, 4, 8, 43, 52, 5234])   # n >= 0
        p = compile_constraint(PowerConstraint(parse_poly('n**3 + 19'), 2))
        self.assertEqual(p.status, NOT_ENUMERATED)
        self.assertNotIn('iter_hits', p.supports)
        with self.assertRaises(NotEnumerable):
            list(p.iter_hits(10))
        with self.assertRaises(NotEnumerable):
            p.count(10)
        with self.assertRaises(NotEnumerable):
            p.all_hits()
        ev = p.bounded_evidence(100)
        self.assertEqual(ev['label'], BOUNDED_EVIDENCE)
        self.assertEqual([n for n, _ in ev['hits']], [5])          # census: (5, ±12)

    def test_execution_is_never_claimed_verified(self):
        for con in (PowerConstraint((1, 0, 2), 2), TriangularConstraint((0, 0, 1))):
            self.assertFalse(compile_constraint(con).explain()['execution_verified'])


class FarHits(unittest.TestCase):
    """COMPLETE_FINITE must be earned: no finite branch may be frozen by a fixed scan limit."""
    C = 10 ** 6 + 7

    def test_quartic_bounded_branches_beyond_scan(self):
        # ((n - c)^2 - 2)^2 = m^4: branches +-((n - c)^2 - 2), a square leading coefficient and a
        # negative one; the hits n = c +- 1 lie beyond any fixed cutoff of 10^6
        W = padd(ppow((-self.C, 1), 2), (-2,))
        p = compile_constraint(PowerConstraint(ppow(W, 2), 4))
        self.assertEqual(p.status, COMPLETE_FINITE)
        self.assertEqual(p.contains(self.C + 1), [-1, 1])
        self.assertEqual(p.all_hits(), [(self.C - 1, [-1, 1]), (self.C + 1, [-1, 1])])
        self.assertIn('PerfectPower.RationalYun.hit_le_of_square', p.justification)

    def test_mixed_pell_program_keeps_late_bounded_hit(self):
        # (2(n - c)^2 - 1)^2 = m^4: a populated Pell branch and a bounded branch hit at n = c
        expr = f'(2*(n - {self.C})**2 - 1)**2'
        sp = specialize(LoopProgram(expr, ('power', 4)))
        self.assertEqual(sp.plan.status, STRUCTURED_INFINITE)
        N = self.C + 20
        window = [(n, sp.plan.original.witnesses(n)) for n in range(self.C - 20, N + 1)]
        window = [h for h in window if h[1]]
        self.assertIn((self.C, [-1, 1]), window)
        self.assertEqual([h for h in sp.run_specialized(N) if h[0] >= self.C - 20], window)
        self.assertEqual([h for h in sp.plan.iter_hits(N) if h[0] >= self.C - 20], window)

    def test_far_shifted_finite_plans(self):
        # shift random small families far out: every hit near the shift must be in the list
        rng = random.Random(7)
        checked = 0
        for _ in range(120):
            G = [rng.randint(-6, 6) for _ in range(rng.choice([1, 2]))] + [rng.choice([-2, -1, 1, 4])]
            d = rng.choice([2, 4])
            shifted = (0,)
            for i, g in enumerate(G):                  # G(n - C)
                shifted = padd(shifted, pscale(ppow((-self.C, 1), i), g))
            F = ppow(shifted, 2) if d == 4 else shifted
            p = compile_constraint(PowerConstraint(F, d))
            if p.status != COMPLETE_FINITE:
                continue
            checked += 1
            listed = {n for n, _ in p.all_hits()}
            for n in range(self.C - 30, self.C + 31):
                self.assertEqual(n in listed, bool(p.original.witnesses(n)), (G, d, n))
        self.assertGreater(checked, 20)


class Differential(unittest.TestCase):
    def test_random_plans_and_programs(self):
        rng = random.Random(20260930)
        seen = set()
        for _ in range(300):
            deg = rng.choice([1, 2, 2, 3])
            F = [rng.randint(-9, 9) for _ in range(deg)] + [rng.choice([-3, -2, -1, 1, 2, 3, 5, 6, 7])]
            expr = ' + '.join(f'({c})*n**{i}' for i, c in enumerate(F))
            dom = rng.choice(['int', 'nonneg', 'pos'])
            test = rng.choice([('power', rng.choice([2, 3])), ('triangular', dom),
                               ('root', rng.choice([-3, -2, -1, 1, 2, 3]), rng.randint(-4, 4),
                                rng.randint(-5, 5), dom)])
            sp = specialize(LoopProgram(expr, test))
            N = 250
            orig = sp.run_original(N)
            self.assertEqual(orig, brute(sp.plan.original, N))
            for n in (1, 2, 5, 17):
                self.assertEqual(sp.plan.contains(n), sp.plan.original.witnesses(n))
            seen.add(sp.plan.status)
            if sp.plan.status == NOT_ENUMERATED:
                self.assertIsNone(sp.source)
                continue
            self.assertEqual(list(sp.plan.iter_hits(N)), orig, (expr, test))
            self.assertEqual(sp.plan.count(N), len(orig))
            if sp.source is not None:
                self.assertEqual(sp.run_specialized(N), orig, (expr, test))
        self.assertTrue({COMPLETE_FINITE, STRUCTURED_INFINITE, NOT_ENUMERATED} <= seen)


class ProofCarrying(unittest.TestCase):
    """The release tests: each case has a generated Lean theorem about the original equation."""

    @classmethod
    def setUpClass(cls):
        import json
        cls.rows = json.loads((ROOT / 'receipts' / 'plan_certificates.json').read_text())
        cls.by_name = {r['theorem'].split('.')[-1]: r for r in cls.rows}

    def test_two_filters_with_certified_count(self):
        # divisibility (|2a| > 2) and the domain y >= 1, composed; its constant is a Lean theorem
        r = self.by_name['plan_filtered_infinite_1']
        self.assertIn('y in Z>=1', r['constraint'])
        self.assertIn('PerfectPower.Generated.Plans.plan_filtered_infinite_1_count', r['also'])

    def test_late_finite_hit_and_both_signs(self):
        r = self.by_name['plan_late_transport']
        self.assertEqual(r['status'], COMPLETE_FINITE)
        self.assertEqual(r['hits'], [[1000007, [-5, 5]]])

    def test_empty_cycle(self):
        r = self.by_name['plan_filtered_finite_2']
        self.assertEqual((r['status'], r['hits']), (COMPLETE_FINITE, []))

    def test_first_hit_beyond_any_scan(self):
        r = self.by_name['plan_far_first_hit']
        self.assertEqual(r['status'], STRUCTURED_INFINITE)
        self.assertIn('PerfectPower.Generated.Plans.plan_far_first_hit_member', r['also'])
        p = compile_constraint(QuadraticRootConstraint(2, 1, 0, (1, 0, 263), 'pos'))
        (n0, ws), = list(p.iter_hits(10 ** 16))[:1]
        self.assertEqual(n0, 7816408648416305)
        self.assertEqual(2 * ws[0] ** 2 + ws[0], 263 * n0 * n0 + 1)
        pt = p.orbit_point(0, 1)
        self.assertEqual((pt['n'], pt['witnesses']), (n0, ws))

    def test_orbit_point_by_exponentiation(self):
        p = compile_constraint(PowerConstraint((1, 0, 2), 2))
        self.assertEqual([p.orbit_point(0, j)['n'] for j in range(1, 5)], [2, 12, 70, 408])
        pt = p.orbit_point(0, 5000)
        self.assertEqual(2 * pt['n'] ** 2 + 1, pt['Y'] ** 2)

    def test_certified_constant_matches_plan(self):
        from fractions import Fraction
        from perfectpower.compiler import count_cert
        for i in range(1, 6):
            r = self.by_name[f'plan_filtered_infinite_{i}']
            if not any(a.endswith('_count') for a in r['also']):
                continue
            # rebuild the constraint from the catalogue and compare sum g / P with the plan
            import sys
            sys.path.insert(0, str(ROOT / 'python'))
            from make_lean_plans import catalogue
            con = dict(catalogue())[f'plan_filtered_infinite_{i}']
            fd = compile_constraint(con).data['filter_decision']
            self.assertEqual(count_cert(con)['sum_g_over_P'], Fraction(fd['good_fraction']))


class Geometry(unittest.TestCase):
    """The passage from recurrence to geometry: each answer is one of three kinds."""

    def test_family_members_are_recognized_and_certified(self):
        from perfectpower.compiler import mordell_family_match
        from perfectpower.arith import factorint
        for k in (1025127, 29115):
            f = mordell_family_match(k)
            self.assertIsNotNone(f)
            c, m, j, m1, u = f['c'], f['m'], f['j'], f['m1'], f['u']
            self.assertEqual((c % 4, 4 * f['t'] - 1), (3, c))
            self.assertEqual(c ** 3 - 4 * m * m, k)
            self.assertEqual((m, (u * u + 1) % m1), (2 ** j * m1, 0))
            # the certificate's consequence, checked directly: no prime = 3 (mod 4) divides m
            self.assertFalse([p for p in factorint(m) if p % 4 == 3])

    def test_family_members_have_no_small_points(self):
        # the Lean theorem says no point at all; sanity-check a window by brute force
        for k in (1025127, 29115):
            for x in range(-_cbrt_floor(k) - 1, 20000):
                r = x ** 3 + k
                self.assertFalse(r >= 0 and math.isqrt(r) ** 2 == r, (k, x))

    def test_family_plans_are_complete_and_empty(self):
        for poly in ('(n + 5)**3 + 1025127', '(2*n + 1)**3 + 29115'):
            p = compile_constraint(PowerConstraint(parse_poly(poly), 2))
            self.assertEqual(p.status, COMPLETE_FINITE)
            self.assertEqual(list(p.iter_hits(10 ** 4)), [])
            self.assertTrue(p.mechanism.startswith('complete finite list'))

    def test_missing_premise_is_explicit(self):
        p = compile_constraint(PowerConstraint(parse_poly('n**3 + 19'), 2))
        self.assertEqual(p.status, NOT_ENUMERATED)
        mp = p.data['missing_premise']
        self.assertIn('Transport.IntegralPointsOnImage', mp['premise'])
        self.assertEqual(mp["model"], "V^2 = U^3 + (0) U + (13851)")
        self.assertTrue(p.mechanism.startswith('missing premise: Transport.IntegralPointsOnImage'))

    def test_counting_law_mechanism(self):
        p = compile_constraint(PowerConstraint((1, 0, 2), 2))
        self.assertTrue(p.mechanism.startswith('infinite family'))

    def test_late_hit_is_certified_first_and_counted(self):
        import json
        rows = json.loads((ROOT / 'receipts' / 'plan_certificates.json').read_text())
        r = {x['theorem'].split('.')[-1]: x for x in rows}['plan_late_certified']
        self.assertIn('PerfectPower.Generated.Plans.plan_late_certified_first', r['also'])
        self.assertIn('PerfectPower.Generated.Plans.plan_late_certified_count', r['also'])
        con = QuadraticRootConstraint(41, 1, 3, (3, 0, 1), 'nonneg')
        (n0, ws), = list(compile_constraint(con).iter_hits(10 ** 6))[:1]
        self.assertEqual((n0, ws), (655680, [102400]))
        text = (ROOT / 'PerfectPower' / 'Generated' / 'Plans.lean').read_text()
        self.assertIn('IsLeast (FilteredPell.QuadHits 41 1 3 1 0 3 (some 0)) 655680', text)


def _cbrt_floor(k):
    r = round(k ** (1 / 3))
    while r ** 3 > k:
        r -= 1
    while (r + 1) ** 3 <= k:
        r += 1
    return r


class Descent(unittest.TestCase):
    """Nonempty complete answers from a discovered descent (Descent.lean)."""

    def test_certificate_for_74(self):
        from perfectpower.descent import certificate
        c = certificate(74)
        self.assertEqual((c['points'], c['class_number'], c['K'], c['j']),
                         ([(99, 985), (99, -985)], 10, 17, [1, 2, 3, 4]))
        self.assertLess(c['r'] ** 2 + 74 * c['t'] ** 2, (c['K'] + 1) * c['r'] * c['t'])
        self.assertLess(c['K'] ** 3, 74 * (c['Q'] + 1) ** 2)

    def test_certificate_is_refused_when_points_are_missing(self):
        # y^2 = x^3 - 11 has (3, +-4) and y^2 = x^3 - 26 has (3, +-1), not of the form
        # (p^2 + D, p^3 - 3Dp); 3 | h for both.  The check must fail.
        from perfectpower.descent import certificate, class_number
        for D in (11, 26):
            self.assertIsNone(certificate(D))
            self.assertEqual(class_number(D) % 3, 0)

    def test_certified_lists_match_brute_force(self):
        from perfectpower.descent import certificate
        for D in range(2, 330):
            c = certificate(D)
            if c is None:
                continue
            found = sorted((x, y) for x in range(1, 3000)
                           for v in [x ** 3 - D] if v >= 0 and math.isqrt(v) ** 2 == v
                           for y in {math.isqrt(v), -math.isqrt(v)})
            self.assertEqual(found, sorted(set(c['points'])), D)

    def test_disguised_input_is_compiled_and_explained(self):
        p = compile_constraint(PowerConstraint(parse_poly('8*n**3 + 12*n**2 + 6*n - 73'), 2))
        self.assertEqual(p.status, COMPLETE_FINITE)
        self.assertTrue(p.method.startswith('descent in Z[sqrt(-74)]'))
        self.assertEqual(p.all_hits(), [(49, [-985, 985])])
        g = p.galois()['descent']
        self.assertEqual((g['field'], g['class_number'], g['units']), ('Q(sqrt(-74))', 10, '{+1, -1}'))
        self.assertIn('prime to 3', g['why'])

    def test_emitted_theorem_and_receipt(self):
        from perfectpower.descent import lean_theorem
        text = lean_theorem('t', 4, 1, 193)
        self.assertIn('Descent.hits_of_cert 193', text)
        self.assertIn('↔ n = 64', text)
        import json
        rows = json.loads((ROOT / 'receipts' / 'plan_certificates.json').read_text())
        r = {x['theorem'].split('.')[-1]: x for x in rows}
        self.assertEqual(r['plan_descent_74']['hits'], [[49, [-985, 985]]])
        self.assertEqual(r['plan_descent_193']['hits'], [[64, [-4120, 4120]]])


class Justification(unittest.TestCase):
    def test_lean_names_exist(self):
        decls = set()
        for path in (ROOT / 'PerfectPower').rglob('*.lean'):
            decls |= set(re.findall(r'^(?:theorem|lemma|def|noncomputable def)\s+(\S+)',
                                    path.read_text(), re.M))
        cases = [PowerConstraint((1, 0, 2), 2), PowerConstraint((0, 1), 3),
                 PowerConstraint(parse_poly('(5*n - 7)**3 - 2'), 2),
                 PowerConstraint(parse_poly('(n + 1)**3 - 5'), 2),
                 PowerConstraint(parse_poly('n**3 - 9985'), 2),
                 TriangularConstraint((0, 0, 1)), QuadraticRootConstraint(2, 1, 0, (0, 1)),
                 PowerConstraint((1, 0, 991), 2),
                 QuadraticRootConstraint(1, 1, 0, parse_poly('16*n**3 - 12*n**2 + 3*n - 1'), 'nonneg'),
                 QuadraticRootConstraint(2, -4, 0, (4, -1, 7), 'int')]
        for con in cases:
            for j in compile_constraint(con).justification:
                j = j.split()[0]
                if j.startswith('PerfectPower.'):
                    last = j.split('.')[-1]
                    qual = '.'.join(j.split('.')[-2:])
                    self.assertTrue(last in decls or qual in decls, j)


if __name__ == '__main__':
    unittest.main()
