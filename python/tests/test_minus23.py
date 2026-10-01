"""The D = 23 pipeline (`python/make_lean_minus23.py`): descent trees, carried leaves, lists."""
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))
sys.path.insert(0, str(ROOT))

import make_lean_minus23 as M  # noqa: E402
from perfectpower import thue_graph as TG  # noqa: E402

REC = json.loads((ROOT / 'receipts' / 'minus23_certificate.json').read_text())


def brute(F, m, B=150):
    return sorted((a, b) for a in range(-B, B + 1) for b in range(-B, B + 1) if TG.evalF(F, a, b) == m)


class TestMinus23(unittest.TestCase):
    def test_unit_equation_lists(self):
        for r in REC['unit_equations']:
            self.assertEqual(sorted(map(tuple, r['list'])), brute(tuple(r['form']), 1))

    def test_phi_norm_identity(self):
        import make_lean_unit_fields as U
        for _, F, phi in M.UNITS:
            for a in range(-6, 7):
                for b in range(-6, 7):
                    self.assertEqual(U.nrm(M.P, M.Q, U.enc(F[0], phi, a, b)), F[0] ** 2 * U.evalF(F, a, b))

    def test_descent_trees(self):
        sources = [(tuple(r['form']), [tuple(x) for x in r['list']]) for r in REC['unit_equations']]
        graph = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
        g = {c['id']: c for c in graph['classes']}
        for r in REC['classes']:
            R, m = tuple(g[r['class']]['representative']), g[r['class']]['M']
            srcs = sources if r['class'] == 10 else sources[:1]
            nodes = M.descent_tree(R, m, srcs)
            # children come after their parents, and every carried leaf is a unimodular transport
            for i, (F, N, k) in enumerate(nodes):
                if k[0] == 'split':
                    kids = ([k[2]] if k[2] is not None else []) + [j for _, _, j in k[3]]
                    self.assertTrue(all(j > i for j in kids))
                if k[0] == 'given':
                    _, c, T, Tinv, s = k
                    self.assertEqual(TG.compose(srcs[c][0], T), tuple(s * x for x in F))
                    self.assertEqual(TG.matmul(Tinv, T), ((1, 0), (0, 1)))
            L = sorted({x for x in M.candidates(nodes, srcs) if TG.evalF(R, *x) == m})
            self.assertEqual(L, sorted(map(tuple, r['list'])))
            self.assertEqual(L, brute(R, m))

    def test_curve_points(self):
        self.assertEqual(sorted(map(tuple, REC['curve']['points'])), [(3, -2), (3, 2)])
        for x, y in REC['curve']['points']:
            self.assertEqual(y * y, x ** 3 - 23)


if __name__ == '__main__':
    unittest.main()
