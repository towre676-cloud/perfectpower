"""Triage of the irreducible positive-k equations (`python/positive_k_next.py`)."""
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))

import positive_k_next as N  # noqa: E402
from perfectpower import thue_graph as TG  # noqa: E402


class Triage(unittest.TestCase):
    def test_summary(self):
        r = json.loads((ROOT / 'receipts' / 'positive_k_next.json').read_text())
        s = r['summary']
        self.assertEqual((s['equations'], s['curves'], s['monic_unit_equations']), (104, 61, 68))

    def test_monic_norm_identity(self):
        # F(u, v) = a N((u + h v) − v z) for z³ + p z + q = 0, checked as polynomials on a grid
        F = (-1, 0, -3, -2)                      # k = 2
        m = N.monic_order(F)
        self.assertEqual((m['p'], m['q']), (3, 2))
        p, q, h, a = m['p'], m['q'], m['u_shift'], m['norm']
        for u in range(-4, 5):
            for v in range(-4, 5):
                x, y = u + h * v, v                  # N(x − y z) = x³ + p x y² + q y³ for z³ = −p z − q
                self.assertEqual(TG.evalF(F, u, v), a * (x ** 3 + p * x * y * y + q * y ** 3))


if __name__ == '__main__':
    unittest.main()
