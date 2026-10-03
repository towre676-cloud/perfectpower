"""`python/lattice_transport.py` (mirror of `LatticeTransport.lean`), checked by brute force."""
import random
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'python'))
import lattice_transport as LT  # noqa: E402

R = range(-40, 41)


def sols(f, M, rng=R):
    return sorted((u, v) for u in rng for v in rng if f((u, v)) == M)


class LatticeTransport(unittest.TestCase):
    def test_counterexample_needs_filter(self):
        F = (2, 1, 0, -1)
        H = LT.monic(F)
        self.assertEqual(LT.cubic(H, (1, 3)), 4 * -26)
        self.assertFalse(LT.lat(((2, 0), (0, 1)), (0, 0), (1, 3)))

    def test_monic_reduction_brute_force(self):
        rnd = random.Random(1)
        for _ in range(30):
            F = (rnd.choice([-3, -2, 2, 3]), rnd.randint(-3, 3), rnd.randint(-3, 3), rnd.randint(-3, 3))
            a = F[0]
            M = rnd.randint(-30, 30)
            H = LT.monic(F)
            # every H-solution with |X| <= a*40 pulls back exactly to the F-solutions with |u| <= 40
            Lh = [(X, Y) for X in range(-abs(a) * 40, abs(a) * 40 + 1) for Y in R
                  if LT.cubic(H, (X, Y)) == a * a * M]
            self.assertEqual(LT.transport(Lh, ((a, 0), (0, 1))), sols(lambda z: LT.cubic(F, z), M))
            self.assertEqual(LT.disc(H), a * a * LT.disc(F))

    def test_affine_transport(self):
        # G(z) = F(Tz + c) / s with det T = 3: the filtered pull-back of F's list is G's list
        F = lambda z: z[0] ** 2 + 2 * z[1] ** 2   # noqa: E731
        T, c, s = ((1, 1), (-1, 2)), (1, 0), 1
        G = lambda z: F((T[0][0] * z[0] + T[0][1] * z[1] + c[0], T[1][0] * z[0] + T[1][1] * z[1] + c[1]))  # noqa: E731
        for M in range(0, 60):
            L = sols(F, s * M, range(-200, 201))
            self.assertEqual(LT.transport(L, T, c), sols(G, M, range(-60, 61)))


if __name__ == '__main__':
    unittest.main()
