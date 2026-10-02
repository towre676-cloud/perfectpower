"""Positive `k` through Mordell's cubic forms (`python/positive_k.py`, `MordellCubicForm.lean`)."""
import json
import random
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))

import positive_k as PK  # noqa: E402
from perfectpower import thue_graph as TG  # noqa: E402


class Correspondence(unittest.TestCase):
    def test_round_trip(self):
        for (x, y, k) in [(2, 3, 1), (-1, 1, 2), (1, 2, 3), (5234, 378661, 17), (2660, 137190, 100)]:
            self.assertEqual(y * y, x ** 3 + k)
            F = PK.form_of_point(x, y)
            self.assertEqual(PK.delta(F), 4 * k)
            self.assertEqual(TG.disc(F), -108 * k)
            T = ((2, 1), (1, 1))
            G = TG.compose(F, T)
            # (1, 0) = T (1, −1)
            self.assertEqual(PK.point_of_rep(G, 1, -1), (x, y))

    def test_delta_invariant_and_covariant(self):
        random.seed(5)
        F = PK.form_of_point(2, 3)
        for _ in range(30):
            while True:
                T = tuple(tuple(random.randint(-3, 3) for _ in range(2)) for _ in range(2))
                if TG.det(T) in (1, -1):
                    break
            G = TG.compose(F, T)
            self.assertEqual(PK.delta(G), 4)
            if G[0]:
                self.assertEqual(PK.canonical(G)[0], PK.canonical(F)[0])

    def test_local_obstruction_exact(self):
        G = (-2, -3, 0, -2)                       # k = 6, class 1 (a, 3b, 3c, d)
        m = PK.local_impossible(G)
        self.assertEqual(m, 9)
        self.assertTrue(all((TG.evalF(G, u, v) - 1) % 9 for u in range(9) for v in range(9)))


class Completeness(unittest.TestCase):
    def test_k17_rational_root_class(self):
        # the class missed by the old stabilizing search: Y(3X² + 17Y²), least leading coefficient 17
        reps, _ = PK.classes(17)
        F = (0, 3, 0, 17)
        key, T = PK.canonical(F)
        self.assertTrue(key in reps or any(PK.equivalent(key, G) for G in reps))

    def test_bound_identities(self):
        # det q = 3/|D| and q(v)^3 >= 27 F(v)^2/|D|^2 on random forms of negative discriminant
        random.seed(3)
        n = 0
        while n < 200:
            F = tuple(random.randint(-9, 9) for _ in range(4))
            D = TG.disc(F)
            if F[0] == 0 or D >= 0:
                continue
            n += 1
            A, B, C = PK.covariant_q(F)
            self.assertAlmostEqual((A * C - B * B / 4) * abs(D), 3, places=6)
            for u, v in ((1, 0), (0, 1), (1, 1), (2, -3)):
                q = A * u * u + B * u * v + C * v * v
                self.assertGreaterEqual(q ** 3 * (1 + 1e-9), 27 * TG.evalF(F, u, v) ** 2 / D ** 2)

    def test_check_complete(self):
        for k in (6, 17, 23, 100):
            reps, _ = PK.classes(k)
            self.assertGreater(PK.check_complete(k, reps), 0)


class Receipt(unittest.TestCase):
    def test_summary(self):
        r = json.loads((ROOT / 'receipts' / 'positive_k.json').read_text())
        s = r['summary']
        self.assertEqual(s['curves'], 100)
        self.assertEqual(s['agree_with_census'], 100)
        self.assertEqual(s['census_points_unmatched'], 0)
        self.assertEqual(len(s['all_classes_locally_impossible']), 25)
        self.assertEqual(s['open_thue_equations'], 158)
        self.assertEqual(s['classes'], 321)
        # a curve with an open-free certificate has no census points
        for row in r['curves']:
            if row['open_thue'] == 0:
                self.assertEqual(row['census_points'], [])
            for c in row['class_detail']:
                self.assertEqual(PK.delta(tuple(c['form'])), 4 * row['k'])

    def test_lean_module(self):
        text = (ROOT / 'PerfectPower' / 'Generated' / 'PositiveK.lean').read_text()
        r = json.loads((ROOT / 'receipts' / 'positive_k.json').read_text())
        for k in r['summary']['all_classes_locally_impossible']:
            self.assertIn(f'theorem plus{k} (hcls : ClassList {k} ', text)
        self.assertNotIn('sorry', text)


if __name__ == '__main__':
    unittest.main()
