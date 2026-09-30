"""Constraint compiler and program specialization (perfectpower.compiler, perfectpower.specialize).

Every plan is checked against the definition by direct evaluation.  The cases target the ways a
reduction can go wrong: a square discriminant whose root is not integral, the sign of the square
root, the domain of the recovered variable, zero and negative values, and finite plans that must
not pose as complete lists.
"""
import random
import re
import unittest
from pathlib import Path

from perfectpower.compiler import (BOUNDED_EVIDENCE, COMPLETE_FINITE, NOT_ENUMERATED,
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

    def test_filter_changes_status(self):
        p = compile_constraint(QuadraticRootConstraint(2, 1, 0, (0, 1), 'nonneg'))
        self.assertEqual(p.status, STRUCTURED_FILTERED)
        self.assertFalse(p.chain[0].filter_trivial)
        self.assertEqual(list(p.iter_hits(60)), [(3, [1]), (10, [2]), (21, [3]), (36, [4]), (55, [5])])

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
        self.assertEqual(compile_constraint(TriangularConstraint((-1, 1), 'pos')).status, STRUCTURED_FILTERED)

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
        p = compile_constraint(PowerConstraint(parse_poly('n**3 + 17'), 2))
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
        self.assertEqual([n for n, _ in ev['hits']], [2, 4, 8, 43, 52])

    def test_execution_is_never_claimed_verified(self):
        for con in (PowerConstraint((1, 0, 2), 2), TriangularConstraint((0, 0, 1))):
            self.assertFalse(compile_constraint(con).explain()['execution_verified'])


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
        self.assertTrue({COMPLETE_FINITE, STRUCTURED_INFINITE, STRUCTURED_FILTERED, NOT_ENUMERATED} <= seen)


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
                 PowerConstraint((1, 0, 991), 2)]
        for con in cases:
            for j in compile_constraint(con).justification:
                if j.startswith('PerfectPower.'):
                    last = j.split('.')[-1]
                    qual = '.'.join(j.split('.')[-2:])
                    self.assertTrue(last in decls or qual in decls, j)


if __name__ == '__main__':
    unittest.main()
