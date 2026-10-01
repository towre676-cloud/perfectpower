"""The layered curve pipeline (`python/make_lean_curves.py`): D = 23 and D = 45."""
import itertools
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))
sys.path.insert(0, str(ROOT))

import make_lean_curves as C  # noqa: E402
import make_lean_unit_fields as U  # noqa: E402
from perfectpower import thue_graph as TG  # noqa: E402


def rec(D):
    return json.loads((ROOT / 'receipts' / f'minus{D}_certificate.json').read_text())


def brute(F, m, B=150):
    return sorted((a, b) for a in range(-B, B + 1) for b in range(-B, B + 1) if TG.evalF(F, a, b) == m)


class TestCurves(unittest.TestCase):
    def test_source_lists(self):
        for D in C.CURVES:
            for s in rec(D)['sources']:
                self.assertEqual(sorted(map(tuple, s['list'])), brute(tuple(s['form']), 1))

    def test_phi_norm_identity(self):
        for cfg in C.CURVES.values():
            for s in cfg['sources']:
                F, phi = s['form'], s['phi']
                for a in range(-6, 7):
                    for b in range(-6, 7):
                        self.assertEqual(U.nrm(cfg['P'], cfg['Q'], U.enc(F[0], phi, a, b)),
                                         F[0] ** 2 * U.evalF(F, a, b))

    def test_residue_normrep(self):
        # replay of NormRepProof.resRepB for the nonmonic source of D = 45
        cfg = C.CURVES[45]
        P, Q = cfg['P'], cfg['Q']
        _, g, m = cfg['sources'][0]['normrep']
        N = cfg['sources'][0]['form'][0] ** 2

        def adj(x):
            A, B, Cc = x
            return ((A + P * Cc) ** 2 - (P * B + Q * Cc) * B, Q * Cc * Cc - A * B, B * B - A * Cc - P * Cc * Cc)
        d = U.nrm(P, Q, g)
        self.assertIn(d, (N, -N))
        for r in itertools.product(range(m), repeat=3):
            if U.nrm(P, Q, r) % m == N % m:
                self.assertTrue(all(c % d == 0 for c in U.mul(P, Q, r, adj(g))), r)
        # a smaller modulus does not suffice: the certificate needs m = 8
        bad = [r for r in itertools.product(range(4), repeat=3)
               if U.nrm(P, Q, r) % 4 == 0 and not all(c % d == 0 for c in U.mul(P, Q, r, adj(g)))]
        self.assertTrue(bad)

    def test_descent_trees(self):
        graph = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
        g = {c['id']: c for c in graph['classes']}
        for D in C.CURVES:
            r = rec(D)
            src = {s['name']: (tuple(s['form']), [tuple(x) for x in s['list']]) for s in r['sources']}
            for cl in r['classes']:
                R, m = tuple(g[cl['class']]['representative']), g[cl['class']]['M']
                srcs = [src[n] for n in cl['sources']]
                nodes = C.descent_tree(R, m, srcs)
                for i, (F, N, k) in enumerate(nodes):
                    if k[0] == 'split':
                        kids = ([k[2]] if k[2] is not None else []) + [j for _, _, j in k[3]]
                        self.assertTrue(all(j > i for j in kids))
                    if k[0] == 'given':
                        _, c, T, Tinv, s = k
                        self.assertEqual(TG.compose(srcs[c][0], T), tuple(s * x for x in F))
                        self.assertEqual(TG.matmul(Tinv, T), ((1, 0), (0, 1)))
                L = sorted({x for x in C.candidates(nodes, srcs) if TG.evalF(R, *x) == m})
                self.assertEqual(L, sorted(map(tuple, cl['list'])))
                self.assertEqual(L, brute(R, m))

    def test_curve_points(self):
        self.assertEqual(sorted(map(tuple, rec(23)['curve_points'])), [(3, -2), (3, 2)])
        self.assertEqual(sorted(map(tuple, rec(45)['curve_points'])), [(21, -96), (21, 96)])

    def test_coverage_is_derived(self):
        cov = json.loads((ROOT / 'receipts' / 'descent_coverage.json').read_text())
        self.assertEqual(cov['unit_equations_registered'] + cov['unit_equations_remaining'],
                         cov['unit_equations_total'])
        reg = {tuple(TG.canonical(tuple(s['form']))[0]) for D in C.CURVES for s in rec(D)['sources']}
        self.assertEqual(cov['unit_equations_registered'],
                         sum(tuple(e['form']) in reg for e in cov['unit_equations']))
        self.assertEqual(sorted(cov['curves_conditionally_complete']), [7, 23, 28, 45, 63])


if __name__ == '__main__':
    unittest.main()
