"""General Weierstrass models: completing the square and trace oracles (`weierstrass_oracle.py`)."""
import random
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import weierstrass_oracle as W  # noqa: E402

# a_p of 11a1 (Cremona; the modular form q ∏ (1 − qⁿ)² (1 − q¹¹ⁿ)²)
AP_11A1 = {2: -2, 3: -1, 5: 1, 7: -2, 13: 4, 17: -2, 19: 0, 23: -1, 29: 0, 31: 7, 37: 3, 41: -8, 43: -6}


def eta_product_coeffs(N):
    """Coefficients of q ∏_{n≥1} (1 − qⁿ)² (1 − q¹¹ⁿ)², exact integer series to q^N."""
    c = [0] * (N + 1)
    c[1] = 1
    for n in range(1, N + 1):
        for m, e in ((n, 2), (11 * n, 2)):
            if m > N:
                continue
            for _ in range(e):
                for k in range(N, m - 1, -1):
                    c[k] -= c[k - m]
    return c


class Weierstrass(unittest.TestCase):
    def test_11a1_traces(self):
        for p, t in AP_11A1.items():
            self.assertEqual(W.ap(W.MODEL_11A1, p), t, p)

    def test_eta_product_independent(self):
        c = eta_product_coeffs(100)
        for p in (2, 3, 5, 7, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97):
            self.assertEqual(W.ap(W.MODEL_11A1, p), c[p], p)

    def test_wrong_coefficient_order_detected(self):
        wrong = (1, -1, 0, -10, -20)
        diffs = sum(W.ap(wrong, p) != AP_11A1[p] for p in AP_11A1 if p != 11)
        self.assertGreater(diffs, 5)

    def test_complete_square_and_readout(self):
        rng = random.Random(7)
        for _ in range(300):
            a = tuple(rng.randint(-5, 5) for _ in range(5))
            x, y = rng.randint(-30, 30), rng.randint(-30, 30)
            a1, a2, a3, a4, _ = a
            a6 = y * y + a1 * x * y + a3 * y - (x ** 3 + a2 * x * x + a4 * x)     # force (x, y) on the curve
            a = (a1, a2, a3, a4, a6)
            self.assertTrue(W.on_curve(a, x, y))
            Y = W.complete_square(a, x, y)
            self.assertEqual(Y * Y, W.quart_rhs(a, x))
            self.assertEqual(W.readout(a, x, Y), y)
            self.assertEqual(W.readout(a, x, -Y), -y - a1 * x - a3)      # the other point


if __name__ == '__main__':
    unittest.main()
