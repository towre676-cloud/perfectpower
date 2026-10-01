"""The field-756 generator's exact arithmetic (`python/make_lean_unit_fields.py`, `UnitBox.lean`)."""
import json
import random
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))

import make_lean_unit_fields as G  # noqa: E402


class TestField756(unittest.TestCase):
    def test_ediv_matches_lean(self):
        # Lean's `Int.ediv`: remainder in [0, |y|)
        rng = random.Random(1)
        for _ in range(2000):
            x, y = rng.randint(-500, 500), rng.choice([v for v in range(-9, 10) if v])
            q = G._tdiv(x, y)
            self.assertTrue(0 <= x - q * y < abs(y))

    def test_dec_enc(self):
        rng = random.Random(2)
        for phi in [(17, 4, -4), (22, 0, -4), (1, 2, 0), (8, 16, 0), (-10, -16, 8)]:
            for c0 in (-4, -3, -1, 2):
                for _ in range(200):
                    a, b = rng.randint(-50, 50), rng.randint(-50, 50)
                    self.assertEqual(G.dec(c0, phi, G.enc(c0, phi, a, b)), (a, b))

    def test_inverse(self):
        for u in [(-5, 0, 1), (11, 1, -2)]:
            self.assertEqual(G.mul(6, 2, u, G.inverse(6, 2, u)), (1, 0, 0))

    def test_receipt_agrees_with_census(self):
        cert = json.loads((ROOT / 'receipts' / 'unit_fields_certificate.json').read_text())['fields'][0]
        for c in cert['classes']:
            self.assertEqual(sorted(map(tuple, c['box_hits'])), sorted(map(tuple, c['list'])))
        self.assertTrue(all(c['agrees_with_sage'] for c in cert['curves']))
        pts = {c['D']: sorted(map(tuple, c['points'])) for c in cert['curves']}
        self.assertEqual(pts[7], [(2, -1), (2, 1), (32, -181), (32, 181)])


    def test_reduction_chains_replay(self):
        from perfectpower import reduction_check as RC
        n = 0
        for name in ('field756_bound.json', 'd72_thue_bound.json'):
            d = json.loads((ROOT / 'receipts' / name).read_text())
            cases = [c for row in d.get('classes', [d]) for c in row['cases']]
            for c in cases:
                enc = RC.enc_from_json(c['enclosure'])
                self.assertTrue(RC.chain_ok(enc, c['M0'], c['steps']))
                n += len(c['steps'])
                # a forged final bound one smaller must fail
                if c['steps']:
                    s = dict(c['steps'][-1]); s['B'] -= 1
                    bad = c['steps'][:-1] + [s]
                    prev = c['steps'][-2]['B'] if len(c['steps']) > 1 else c['M0']
                    if s['B'] >= 0 and not RC.step_ok(enc, prev, s['q'], s['B'], s['J']):
                        self.assertFalse(RC.chain_ok(enc, c['M0'], bad))
        self.assertGreater(n, 40)


if __name__ == '__main__':
    unittest.main()
