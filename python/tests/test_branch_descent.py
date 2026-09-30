"""The branch compiler for y^2 = x^3 - D (`branch_descent.py`) against independent computations."""
import csv
import json
import unittest
from math import isqrt
from pathlib import Path

from perfectpower.branch_descent import (branch_ys, compile_curve, cube_witness, icbrt,
                                         local_obstruction, table)
from perfectpower.descent import W1, W2

ROOT = Path(__file__).resolve().parents[2]


def scan(D, X=20000):
    out = set()
    for x in range(1, X):
        v = x ** 3 - D
        if v >= 0 and isqrt(v) ** 2 == v:
            out |= {(x, isqrt(v)), (x, -isqrt(v))}
    return out


class Branches(unittest.TestCase):
    def test_gaussian_pilot(self):
        c = compile_curve(1)
        self.assertEqual(c['status'], 'COMPLETE')
        self.assertEqual(c['points'], [(1, 0)])
        # the units +-i are cubes (i = (-i)^3) and 2 + 2i = (i - 1)^3
        self.assertEqual(cube_witness(1, 1, 0, 1), (0, -1, 1))
        self.assertEqual(cube_witness(1, 2, 2, 2), (-1, 1, 1))

    def test_table_is_every_representation(self):
        for D in (7, 26, 76):
            K, Q = 12, 6
            got = set(table(D, K, Q))
            brute = {(k, p, q) for k in range(1, K + 1) for q in range(-Q, Q + 1)
                     for p in range(-60, 61) if p * p + D * q * q == k ** 3}
            self.assertEqual(got, brute)

    def test_branch_values_by_brute_force(self):
        # every (A, B) with B (3A^2 - D B^2) = M in a box gives a listed y
        for D, M in ((7, 8), (11, 27), (19, 64)):
            ys = set(branch_ys(D, round(M ** (1 / 3)), 1))
            for B in range(-M, M + 1):
                for A in range(-200, 201):
                    if B and B * (3 * A * A - D * B * B) == M and (A ** 3 - 3 * D * A * B * B) % M == 0:
                        self.assertIn((A ** 3 - 3 * D * A * B * B) // M, ys)

    def test_local_obstruction_is_sound(self):
        m = local_obstruction(31, 5, 9, 2)
        self.assertIsNotNone(m)
        for a in range(-40, 41):
            for b in range(-40, 41):
                self.assertNotEqual(2 * W1(31, a, b) - 9 * W2(31, a, b), 125)

    def test_complete_curves_match_scan_and_census(self):
        census = {}
        with open(ROOT / 'data' / 'mordell_census.csv') as f:
            for row in csv.DictReader(f):
                census[int(row['k'])] = sorted(int(v) for v in row['x_coordinates'].split())
        for D in (1, 8, 11, 19, 35, 44, 76, 81):
            c = compile_curve(D)
            self.assertEqual(c['status'], 'COMPLETE', D)
            self.assertEqual(set(c['points']), scan(D), D)
            self.assertEqual(sorted({x for x, _ in c['points']}), census[-D], D)

    def test_open_curve_is_not_counted(self):
        c = compile_curve(7)                      # (2, +-1), (32, +-181) come from Thue branches
        self.assertEqual(c['status'], 'OPEN_BRANCH')
        self.assertTrue(c['open'])

    def test_receipts(self):
        r = json.loads((ROOT / 'receipts' / 'mordell_branch.json').read_text())
        self.assertEqual(r['complete'], 26)
        self.assertEqual(r['complete_agree_with_sage'], 26)
        t = json.loads((ROOT / 'receipts' / 'mordell_branch_thue.json').read_text())
        self.assertEqual(t['externally_complete'], len(t['curves']))
        self.assertEqual(t['agree_with_sage'], len(t['curves']))

    def test_icbrt(self):
        for n in (-30, -27, -1, 0, 1, 26, 27, 28, 10 ** 30):
            r = icbrt(n)
            self.assertTrue(r ** 3 <= n < (r + 1) ** 3)


if __name__ == '__main__':
    unittest.main()
