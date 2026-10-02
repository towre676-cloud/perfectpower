"""Certificates for the class-list premise (`python/class_list_cert.py`, `ClassListProof.lean`)."""
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))

import class_list_cert as CL  # noqa: E402
from perfectpower import thue_graph as TG  # noqa: E402


class ClassListCert(unittest.TestCase):
    def test_act_mirrors_compose(self):
        F = (1, 0, -2, -6)
        for T in (((2, 1), (1, 1)), ((0, 1), (1, 0)), ((1, 3), (0, 1)), ((-1, 2), (1, -3))):
            (p, q), (r, s) = T
            G = CL.act(F, p, q, r, s)
            std = TG.compose((F[0], 3 * F[1], 3 * F[2], F[3]), T)
            self.assertEqual((G[0], 3 * G[1], 3 * G[2], G[3]), std)
            self.assertEqual(CL.delta(G), CL.delta(F) * (p * s - q * r) ** 6)

    def test_params_exact(self):
        for k in (1, 6, 50, 100):
            P = CL.params(k)
            D = 108 * k
            self.assertLessEqual(D ** 2 * P['s0'] ** 3, 27)
            self.assertLessEqual(4, D * P['s1'] ** 2)
            self.assertLessEqual(D ** 2 * P['H'] ** 3, 27 * P['M'] ** 2)
            self.assertLessEqual(4 * k, P['bmax'] ** 2)

    def test_box_forms_complete_and_certified(self):
        # every box form found by an independent brute force over d is in box_forms, and certified
        k = 6
        P = CL.params(k)
        forms = set(CL.box_forms(k, P['amax'], P['bmax']))
        brute = {(a, b, c, d) for a in range(-P['amax'], P['amax'] + 1) for b in range(-P['bmax'], P['bmax'] + 1)
                 for c in range(-P['bmax'], P['bmax'] + 1) for d in range(-400, 401)
                 if CL.delta((a, b, c, d)) == 4 * k}
        self.assertEqual(forms, brute)

    def test_receipt(self):
        r = json.loads((ROOT / 'receipts' / 'class_lists.json').read_text())
        ks = [c['k'] for c in r['curves']]
        self.assertEqual(len(ks), 39)
        for c in r['curves']:
            self.assertTrue((ROOT / 'PerfectPower' / 'Generated' / 'ClassLists' / f"K{c['k']}.lean").exists())

    def test_k2_box_certified(self):
        # the k = 2 module (`Generated/ClassLists/K2.lean`): every box form has a transport
        P, certs = CL.build(2, [(-1, 0, -1, -2), (0, -1, 0, -2)])
        self.assertEqual((P['amax'], P['bmax'], len(certs)), (3, 8, 110))
        for F, G, p, q, r, s in certs:
            self.assertEqual(CL.act(G, p, q, r, s), F)
        self.assertTrue((ROOT / 'PerfectPower' / 'Generated' / 'ClassLists' / 'K2.lean').exists())

    def test_plus2_source_data(self):
        # Python-only sanity checks of the data in `Plus2.lean` (the proof is in Lean)
        def mul(x, y):  # z^3 = -3z - 2
            a, b, c = x
            d, e, f = y
            c0, c1, c2, c3, c4 = a * d, a * e + b * d, a * f + b * e + c * d, b * f + c * e, c * f
            # z^4 = -3z^2 - 2z
            c2 += -3 * c4
            c1 += -2 * c4
            return (c0 - 2 * c3, c1 - 3 * c3, c2)
        eta, eps = (17, -3, 5), (1, 1, -1)
        self.assertEqual(mul(eta, eps), (1, 0, 0))
        x, y = (1, 0, 0), (1, 0, 0)
        for n in range(1, 60):
            x, y = mul(x, eta), mul(y, eps)
            self.assertNotEqual(x[2], 0)
            self.assertNotEqual(y[2], 0)
        sols = [(u, v) for u in range(-60, 61) for v in range(-60, 61)
                if -u ** 3 - 3 * u * v * v - 2 * v ** 3 == 1]
        self.assertEqual(sols, [(-1, 0)])


if __name__ == '__main__':
    unittest.main()
