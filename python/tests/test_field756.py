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


    @staticmethod
    def _cases():
        out = []
        for name in ('field756_bound.json', 'd72_thue_bound.json'):
            d = json.loads((ROOT / 'receipts' / name).read_text())
            out += [c for row in d.get('classes', [d]) for c in row['cases']]
        return out

    def test_reduction_chains_replay(self):
        from perfectpower import reduction_check as RC
        cases = self._cases()
        self.assertEqual(len(cases), 24)
        self.assertEqual(sum(len(c['steps']) for c in cases), 56)
        for c in cases:
            enc = RC.enc_from_json(c['enclosure'])
            self.assertTrue(RC.chain_ok(enc, c['M0'], c['steps']))
            self.assertEqual(RC.chain_end(c['M0'], c['steps']), c['H_reduced'])

    def test_forged_final_bound_rejected(self):
        """Every stored final bound, reduced by one, is rejected (no conditional skip)."""
        from perfectpower import reduction_check as RC
        for c in self._cases():
            enc = RC.enc_from_json(c['enclosure'])
            last = dict(c['steps'][-1])
            last['B'] -= 1
            self.assertGreaterEqual(last['B'], 0)
            self.assertFalse(RC.chain_ok(enc, c['M0'], c['steps'][:-1] + [last]), c['H0'])

    def test_degenerate_steps_rejected(self):
        """A zero denominator, zero Taylor terms or zero decay never certify a step."""
        from fractions import Fraction
        from perfectpower import reduction_check as RC
        for c in self._cases():
            enc = RC.enc_from_json(c['enclosure'])
            s = c['steps'][0]
            self.assertTrue(RC.step_ok(enc, c['M0'], s['q'], s['B'], s['J']))
            self.assertFalse(RC.step_ok(enc, c['M0'], 0, s['B'], s['J']))       # q = 0
            self.assertFalse(RC.step_ok(enc, c['M0'], s['q'], s['B'], 0))       # J = 0: empty sum
            flat = dict(enc, cl=Fraction(0))                                    # c = 0: sum is 1
            self.assertFalse(RC.step_ok(flat, c['M0'], s['q'], s['B'], s['J']))
            wide = dict(enc, kl=enc['kl'] - 1)                                  # κ enclosure too wide
            self.assertFalse(RC.step_ok(wide, c['M0'], s['q'], s['B'], s['J']))


if __name__ == '__main__':
    unittest.main()
