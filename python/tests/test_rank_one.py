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
        rec = {r['k']: r for r in json.loads((ROOT / 'receipts' / 'rank_one_sources.json').read_text())['sources']}
        self.assertEqual(sorted(rec), [4, 33, 49, 81])
        for k, P, Q, start in R1.TARGETS:
            r = R1.find(k, P, Q, start)
            self.assertEqual(r['eta'], rec[k]['eta'])
            self.assertEqual(R1.mul(P, Q, tuple(r['eta']), tuple(r['eps'])), (1, 0, 0))
            self.assertEqual(R1.nrm(P, Q, tuple(r['eta'])), 1)
            # the handoff's start unit is ε = η⁻¹
            self.assertEqual(tuple(r['eps']), start)
            self.assertLessEqual(r['slab_elements'], 40)
            self.assertEqual((r['skolem_eta']['p'], r['skolem_eta']['M']), (3, 3))

    def test_source_brute_force(self):
        # Python-only: no other solution of −u³ + P u v² + Q v³ = 1 with |u|, |v| ≤ 150
        for k, P, Q, _ in R1.TARGETS:
            sols = [(u, v) for u in range(-150, 151) for v in range(-150, 151)
                    if -u ** 3 + P * u * v * v + Q * v ** 3 == 1]
            self.assertEqual(sols, [(-1, 0)], k)

    def test_z2_coordinate_nonzero(self):
        # Python-only spot check of the Lean zero set: the z² coordinate of η^n, |n| ≤ 40
        for k, P, Q, _ in R1.TARGETS:
            r = R1.find(k, P, Q, R1.TARGETS[[t[0] for t in R1.TARGETS].index(k)][3])
            x = y = (1, 0, 0)
            for _ in range(40):
                x, y = R1.mul(P, Q, x, tuple(r['eta'])), R1.mul(P, Q, y, tuple(r['eps']))
                self.assertNotEqual(x[2], 0)
                self.assertNotEqual(y[2], 0)

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
