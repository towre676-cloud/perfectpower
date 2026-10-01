"""Exact regression examples recovered from old notes (`docs/ARCHIVE_SALVAGE.md`), and the projector
certificate checker (`perfectpower.power_certificate`, Lean: `PowerCertificate.lean`).  Ported from
the archive salvage review; exact `Fraction` arithmetic except the quadrature cross-check."""
import math
import sys
import unittest
from fractions import Fraction as Q
from itertools import permutations, product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from perfectpower import power_certificate as PC  # noqa: E402


def mpow(a, n):
    out = [[Q(int(i == j)) for j in range(len(a))] for i in range(len(a))]
    for _ in range(n):
        out = PC.mm(out, a)
    return out


def det(a):
    n = len(a)
    return sum((-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n))
               * math.prod(a[i][p[i]] for i in range(n)) for p in permutations(range(n)))


class ProjectorCertificate(unittest.TestCase):
    M = [[Q(1), Q(1, 2)], [Q(0), Q(1, 2)]]
    P = [[Q(1), Q(1)], [Q(0), Q(0)]]

    def test_svd_counterexample(self):
        # singular values 1 and 0, yet M² = 0: singular values do not determine powers
        n = [[0, 1], [0, 0]]
        self.assertEqual(PC.mm([[0, 0], [1, 0]], n), [[0, 0], [0, 1]])
        self.assertEqual(PC.mm(n, n), [[0, 0], [0, 0]])

    def test_valid_oblique_certificate(self):
        self.assertTrue(PC.check(self.M, self.P, Q(1, 2)))
        self.assertNotEqual(self.P, [list(r) for r in zip(*self.P)])     # oblique
        t = PC.sub(self.M, self.P)
        for k in range(1, 65):
            mk = mpow(self.M, k)
            self.assertEqual(mk, [[a + b for a, b in zip(r1, r2)] for r1, r2 in zip(self.P, mpow(t, k))])
            self.assertLessEqual(PC.norm_inf(PC.sub(mk, self.P)), Q(1, 2) ** k)

    def test_rejections(self):
        self.assertFalse(PC.check(self.M, [[Q(1), Q(0)], [Q(0), Q(0)]], Q(1, 2)))   # forged projector
        self.assertFalse(PC.check(self.M, self.P, Q(1, 4)))                          # understated bound
        self.assertFalse(PC.check(self.M, self.P, 0.5))                              # binary float
        self.assertFalse(PC.check(self.M, self.P, Q(1)))                             # not a contraction

    def test_steps(self):
        self.assertEqual(PC.steps_for(Q(1, 2), Q(1, 1024)), 10)
        self.assertEqual(PC.steps_for(0, Q(1, 10)), 1)                              # boundary ρ = 0
        for rho, eps in ((1, Q(1, 2)), (Q(1, 2), 0), (0, -1)):                      # would not terminate
            with self.assertRaises(ValueError):
                PC.steps_for(rho, eps)
        for rho, eps in ((0.5, Q(1, 2)), (True, Q(1, 2)), (Q(1, 2), 0.1)):
            with self.assertRaises(TypeError):
                PC.steps_for(rho, eps)
        self.assertGreater(Q(95, 100) ** 3, Q(85, 100))      # 0.95³ ≈ 0.857 is not negligible


class ExactExamples(unittest.TestCase):
    def test_golden_determinant_335(self):
        def mul(a, b):                     # ℤ[φ], φ² = φ + 1, as (x, y) = x + yφ
            return (a[0] * b[0] + a[1] * b[1], a[0] * b[1] + a[1] * b[0] + a[1] * b[1])

        def pw(n):
            out, base = (1, 0), ((0, 1) if n >= 0 else (-1, 1))
            for _ in range(abs(n)):
                out = mul(out, base)
            return out
        ex = [[8, -4, -6, 2], [7, -3, -5, 1], [4, -7, 3, 6], [-1, -2, -8, 5]]
        tot = (0, 0)
        for perm in permutations(range(4)):
            s = (-1) ** sum(perm[i] > perm[j] for i in range(4) for j in range(i + 1, 4))
            t = (1, 0)
            for i in range(4):
                t = mul(t, pw(ex[i][perm[i]]))
            tot = (tot[0] + s * t[0], tot[1] + s * t[1])
        self.assertEqual(tot, (335, 0))

    def test_plastic_order_and_padovan(self):
        def cmul(a, b):                    # α³ = α + 1
            p = [0] * 5
            for i in range(3):
                for j in range(3):
                    p[i + j] += a[i] * b[j]
            return (p[0] + p[3], p[1] + p[3] + p[4], p[2] + p[4])
        self.assertEqual(cmul((0, 1, 0), (-1, 0, 1)), (1, 0, 0))        # α⁻¹ = α² − 1
        pad = {0: 1, 1: 1, 2: 1}
        for k in range(3, 101):
            pad[k] = pad[k - 2] + pad[k - 3]
        for k in range(-1, -101, -1):
            pad[k] = pad[k + 3] - pad[k + 1]
        for n in range(-98, 98):
            self.assertEqual(pad[n + 3], pad[n + 1] + pad[n])
        self.assertEqual([pad[i] for i in range(10)], [1, 1, 1, 2, 2, 3, 4, 5, 7, 9])
        self.assertEqual(det([[0, 1, 0], [0, 0, 1], [1, 1, 0]]), 1)

    def test_fir_moment_certificate(self):
        stencil = [-2, -1, 0, 1, 2]
        w = [Q(1, 12), Q(-2, 3), Q(0), Q(2, 3), Q(-1, 12)]
        self.assertEqual([sum(c * Q(j) ** k for j, c in zip(stencil, w)) for k in range(5)], [0, 1, 0, 0, 0])
        bad = w[:]
        bad[0] += Q(1, 12)
        self.assertNotEqual(sum(bad), 0)

    def test_localization_and_cocycle(self):
        self.assertEqual(10 * Q(30, 13) - 23, Q(1, 13))      # ℤ[30/13] = ℤ[1/13]
        cube = list(product(range(2), repeat=3))
        image = {((u + v) % 2, (v + w) % 2, (w + u) % 2) for u, v, w in cube}
        self.assertEqual(image, {x for x in cube if sum(x) % 2 == 0})     # H¹ = 0 on the filled triangle

    def test_projected_input_not_safe(self):
        # a projected (safe-looking) input can still drive the state into the bad mode
        self.assertEqual(PC.mm([[0, 0], [1, 0]], [[1], [0]]), [[0], [1]])

    def test_integral_closed_form(self):
        # ∫₀^∞ cos²(ax)/(1 + x⁴) dx, which equals the whole-line integral of integ.txt (symmetrizing
        # removes the 1/(1 + 4^x) weight) — a numerical cross-check of the closed form, not a certificate
        for a in (0, 0.5, 1, 2):
            s = math.sqrt(2) * abs(a)
            closed = math.pi / (4 * math.sqrt(2)) * (1 + math.exp(-s) * (math.cos(s) + math.sin(s)))
            h, n = 0.005, 40000
            f = lambda x: math.cos(a * x) ** 2 / (1 + x ** 4)  # noqa: E731
            simpson = h / 3 * (f(0) + f(n * h) + math.fsum((4 if k % 2 else 2) * f(k * h) for k in range(1, n)))
            self.assertLess(abs(closed - simpson), 1e-6)


if __name__ == '__main__':
    unittest.main()
