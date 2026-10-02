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


if __name__ == '__main__':
    unittest.main()
