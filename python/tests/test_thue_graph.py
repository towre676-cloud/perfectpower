"""The Thue workload as a transformation graph (`thue_graph.py`, `make_lean_thue_branch.py`)."""
import importlib.util
import json
import random
import unittest
from pathlib import Path

from perfectpower import thue_graph as G

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('mltb', ROOT / 'python' / 'make_lean_thue_branch.py')
mltb = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mltb)


def check_desc(p, nodes):
    """A Python mirror of `ThueLocal.descB` (the Lean checker is authoritative)."""
    for i, (F, M, k) in enumerate(nodes):
        if k[0] == 'leaf':
            r = mltb.lift_obstruction(F, M, p, k[1])
            if not r or r[0] != k[1]:
                return False
            continue
        _, zero, lines = k
        if M % p:
            return False
        if zero is None:
            if M % p ** 3 == 0:
                return False
        elif not (zero > i and nodes[zero][:2] == (F, M // p ** 3)):
            return False
        for a0 in range(p):
            for b0 in range(p):
                if (a0, b0) == (0, 0) or G.evalF(F, a0, b0) % p:
                    continue
                if not any((l is not None and (a0 - l * b0) % p == 0) or (l is None and b0 % p == 0)
                           for l, s, j in lines):
                    return False
        for l, s, j in lines:
            H = G.compose(F, mltb.line_mat(p, l))
            if j <= i or any(c % p ** s for c in H) or M % p ** s:
                return False
            if nodes[j][:2] != (tuple(c // p ** s for c in H), M // p ** s):
                return False
    return True


class Graph(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.g = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())

    def test_canonical_is_invariant(self):
        random.seed(7)
        gens = [((1, 1), (0, 1)), ((1, -1), (0, 1)), ((0, 1), (1, 0)), ((1, 0), (1, 1)), ((-1, 0), (0, 1))]
        for c in random.sample(self.g['classes'], 20):
            F = tuple(c['representative'])
            for _ in range(5):
                T = ((1, 0), (0, 1))
                for _ in range(6):
                    T = G.matmul(T, random.choice(gens))
                self.assertEqual(G.canonical(G.compose(F, T))[0], G.canonical(F)[0])

    def test_edges_are_exact(self):
        for c in self.g['classes']:
            for m in c['members']:
                T = (tuple(m['T'][0]), tuple(m['T'][1]))
                self.assertIn(G.det(T), (1, -1))
                self.assertEqual(list(G.compose(tuple(m['F']), T)), c['representative'])

    def test_compression(self):
        s = self.g['summary']
        self.assertEqual((s['nodes'], s['classes'], s['class_sizes']), (316, 79, [4]))
        self.assertEqual(s['classes_shared_across_curves'], 0)

    def test_certificates_check(self):
        for c in self.g['classes']:
            if 'descent' not in c:
                continue
            d = c['descent']
            nodes = [(tuple(F), M, ('leaf', k[1]) if k[0] == 'leaf' else
                      ('split', k[1], [tuple(x) for x in k[2]])) for F, M, k in d['certificate']]
            self.assertEqual(nodes[0][:2], (tuple(c['representative']), c['M']))
            self.assertTrue(check_desc(d['p'], nodes), c['id'])

    def test_no_certificate_for_point_carrying_classes(self):
        for c in self.g['classes']:
            if c['pari_label'] == 'carries_points':
                self.assertNotIn('descent', c)
        # e.g. D = 7: its Thue branches carry (2, +-1) and (32, +-181)
        rep = next(c for c in self.g['classes'] if 7 in c['curves'])
        self.assertIsNone(mltb.descent(tuple(rep['representative']), rep['M'], 3))

    def test_closed_curves(self):
        closed = [r for r in self.g['curves'] if r['status'] == 'COMPLETE']
        self.assertEqual([r['D'] for r in closed], [29, 32, 36, 38, 52, 56, 77, 80, 86, 92])
        self.assertTrue(all(r['agrees_with_sage'] for r in closed))
        self.assertEqual(next(r for r in closed if r['D'] == 56)['points'], [[18, -76], [18, 76]])   # 18^3 - 56 = 76^2


if __name__ == '__main__':
    unittest.main()
