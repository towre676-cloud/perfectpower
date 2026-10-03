"""Rank-one sources (`python/rank_one_sources.py`, `RankOne.lean`) and the second OEIS handoff
(`python/skolem3_scan.py`, `python/positive_k_oeis.py`).  Python-only checks; the proofs are in Lean."""
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))

import positive_k_oeis as PKO  # noqa: E402
import rank_one_sources as R1  # noqa: E402
import skolem3_scan as SK  # noqa: E402


class RankOne(unittest.TestCase):
    def test_sources_match_receipt(self):
        rec = {(r['k'], tuple(r.get('witness_form', r['form']))): r for r in
               json.loads((ROOT / 'receipts' / 'rank_one_sources.json').read_text())['sources']}
        self.assertEqual(len(rec), len(R1.TARGETS))
        for k, F, P, Q, h, eta, *U in R1.TARGETS:
            r = rec[(k, F)]
            if U:
                self.assertEqual(r['U'], [list(U[0][0]), list(U[0][1])])
                R1.witness_check(F, U[0], P, Q)
                F = (-1, 0, P, Q)
            self.assertEqual(tuple(r['eta']), eta)
            self.assertEqual(R1.mul(P, Q, tuple(r['eta']), tuple(r['eps'])), (1, 0, 0))
            self.assertEqual(R1.nrm(P, Q, eta), 1)
            self.assertEqual(r['skolem_eta']['p'], r['skolem_eps']['p'])
            # F(u, v) = −N((u + hv) − vz)
            for u in range(-3, 4):
                for v in range(-3, 4):
                    w = u + h * v
                    a, B, C, d = F
                    self.assertEqual(a * u ** 3 + B * u * u * v + C * u * v * v + d * v ** 3,
                                     -R1.nrm(P, Q, (w, -v, 0)))
        # the handoff's p = 3 candidates are the inverses of the proved fundamental units
        for k, start in ((4, (1, -1, -1)), (33, (3, 1, -1)), (49, (1, -2, -1)), (81, (1, 3, 1))):
            self.assertEqual(tuple(next(r for (kk, _), r in rec.items() if kk == k)['eps']), start)

    def test_source_brute_force(self):
        # Python-only: no other solution of F(u, v) = 1 with |u|, |v| ≤ 120
        for k, (a, B, C, d), P, Q, h, _, *U in R1.TARGETS:
            sols = [(u, v) for u in range(-120, 121) for v in range(-120, 121)
                    if a * u ** 3 + B * u * u * v + C * u * v * v + d * v ** 3 == 1]
            # a witness source has only its recorded point, the first column of U negated
            self.assertEqual(sols, [(-U[0][0][0], -U[0][1][0])] if U else [(-1, 0)], k)

    def test_z2_coordinate_nonzero(self):
        # Python-only spot check of the Lean zero set: the z² coordinate of η^n, 0 < |n| ≤ 30
        for k, F, P, Q, h, eta, *_ in R1.TARGETS:
            eps = R1.inverse(P, Q, eta)
            x = y = (1, 0, 0)
            for _ in range(30):
                x, y = R1.mul(P, Q, x, eta), R1.mul(P, Q, y, eps)
                self.assertNotEqual(x[2], 0)
                self.assertNotEqual(y[2], 0)

    def test_witness_monic(self):
        # review item 1: every recorded point of a nonmonic source normalizes to leading −1
        import witness_monic as W
        rec = json.loads((ROOT / 'receipts' / 'witness_monic.json').read_text())
        self.assertEqual(rec['summary']['nonmonic_sources'], 36)
        self.assertEqual(rec['summary']['with_witness'], 19)
        for r in rec['sources']:
            for rep in r['known_representations']:
                U, G, mo = W.normalize(tuple(r['form']), tuple(rep))
                self.assertEqual(G[0], -1)
                self.assertEqual(mo['u_shift'], 0)
                (al, be), (ga, de) = U
                self.assertEqual(al * de - be * ga, 1)
        ready = {(r['k'], tuple(r['form'])) for r in rec['sources'] if r['status'] == 'ready'}
        targets = {(k, F) for k, F, *rest in R1.TARGETS if len(rest) == 5}
        self.assertEqual(ready, targets)

    def test_skolem_scan_receipt(self):
        out = SK.scan(ROOT / 'receipts' / 'positive_k_next.json', 6)
        rec = json.loads((ROOT / 'receipts' / 'skolem3_candidates.json').read_text())
        self.assertEqual(out, rec)
        self.assertEqual(rec['summary'], {'monic_sources': 68, 'one_source_curves_with_p3_candidate': 5,
                                          'with_p3_candidate': 9})

    def test_oeis_crosscheck(self):
        r = PKO.run()
        self.assertEqual(r['summary']['curves'], 100)
        self.assertEqual(r['summary']['mismatches'], 0)
        self.assertEqual(r['summary']['census_only_rows'] + len(r['summary']['lean_complete']), 100)
        self.assertIn(2, r['summary']['lean_complete'])


if __name__ == '__main__':
    unittest.main()


class Atlas(unittest.TestCase):
    def test_gap_atlas(self):
        import gap_atlas as GA
        r = GA.run()
        rows = {x['k']: x for x in r['rows']}
        self.assertEqual(rows[1]['square_above_cube']['solutions'], [[3, 2]])     # Catalan: 3^2 - 2^3 = 1
        self.assertEqual(rows[2]['cube_above_square']['solutions'], [[5, 3]])     # 3^3 - 5^2 = 2
        self.assertEqual(rows[2]['cube_above_square']['status'], 'lean')          # MordellMinus2.points
        self.assertEqual(rows[2]['square_above_cube']['solutions'], [])          # K2.plus2: only x = -1
        self.assertEqual(sum(r['summary']['directions_by_status'].values()), 200)
        for x in r['rows']:
            for key in ('square_above_cube', 'cube_above_square'):
                for a, b in x[key]['solutions']:
                    self.assertEqual(a * a - b ** 3, x['k'] if key == 'square_above_cube' else -x['k'])

    def test_registry_sections(self):
        reg = json.loads((ROOT / 'receipts' / 'mordell_registry.json').read_text())
        self.assertTrue(all(c['premises'] == [] for c in reg['positive_curves']))
        self.assertTrue(all(c['premises'] and all('matveev' in p for p in c['premises'])
                            for c in reg['conditional_curves']))
        self.assertFalse({c['k'] for c in reg['positive_curves']} & {-c['D'] for c in reg['conditional_curves']})
