"""The unconditional descent instances agree with the independent Mordell census."""
import csv
import json
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class DescentAgreesWithCensus(unittest.TestCase):
    def test_every_descent_curve_has_no_census_points(self):
        rec = json.loads((ROOT / 'receipts' / 'mordell_descent.json').read_text())
        census = {int(r['k']): r for r in csv.DictReader((ROOT / 'data' / 'mordell_census.csv').open())}
        self.assertGreater(rec['curves'], 1000)
        for r in rec['rows']:
            k, D, c, b = r['k'], r['D'], r['c'], r['b']
            self.assertEqual(k, c ** 3 - D * b * b)
            self.assertEqual(b, 2 ** r['j'] * r['b1'])
            self.assertEqual((r['u'] ** 2 + D) % r['b1'], 0)
            self.assertEqual(census[k]['n_points_up_to_sign'], '0', k)

    def test_small_scan(self):
        rec = json.loads((ROOT / 'receipts' / 'mordell_descent.json').read_text())
        ks = {r['k'] for r in rec['rows'] if abs(r['k']) <= 200}
        squares = {y * y for y in range(0, 3000)}
        for k in ks:
            for x in range(-60, 2000):
                self.assertNotIn(x ** 3 + k, squares, (k, x))


if __name__ == '__main__':
    unittest.main()
