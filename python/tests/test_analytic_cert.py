"""The exact replay of `AnalyticBridge.caseCompute`/`caseOK` (`perfectpower.analytic_cert`)."""
import json
import math
import sys
import unittest
from fractions import Fraction as Fr
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower import analytic_cert as AC  # noqa: E402

D72 = json.loads((ROOT / 'receipts' / 'd72_thue_bound.json').read_text())


def _d72():
    d = D72
    return (d['P'], d['Q'], tuple(d['form']), 1, tuple(d['phi']), tuple(d['gammas'][0]),
            tuple(d['units'][0]), tuple(d['units'][1]), d['V0'])


class TestIntervals(unittest.TestCase):
    def test_log_encloses(self):
        p, J = 192, 63
        for y in (Fr(7, 3), Fr(1, 1000), Fr(10 ** 9 + 7), Fr(3, 2), Fr(2)):
            self.assertTrue(AC.logOK(p, AC.ofQ(y)))
            lo, hi = AC.logI(p, J, AC.ofQ(y))
            v = math.log(y.numerator) - math.log(y.denominator)
            self.assertLessEqual(float(lo), v + 1e-12)
            self.assertGreaterEqual(float(hi), v - 1e-12)
            self.assertLess(hi - lo, Fr(1, 2 ** 180))

    def test_exp_upper(self):
        for r in (Fr(0), Fr(1, 2), Fr(37, 10), Fr(185, 10)):
            self.assertGreaterEqual(float(AC.expHi(192, 12, r)), math.exp(r) * (1 - 1e-15))

    def test_red(self):
        for y in (Fr(1), Fr(5, 7), Fr(1024), Fr(1023, 1024), Fr(3, 10 ** 30)):
            m, w = AC.red(y)
            self.assertTrue(1 <= w < 2)
            self.assertEqual(w * Fr(2) ** m, y)


class TestCertificate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.args = _d72()
        cls.cert = AC.class_cert(*cls.args)
        P, Q, F, M, phi, g0, e1, e2, _ = cls.args
        cls.Nq = Fr(abs(F[0] ** 2 * M))
        cls.bases = [AC.baseOf(cls.cert['p'], cls.cert['lo'], cls.cert['hi'], phi, g0, e1, e2, i)
                     for i in range(3)]

    def _ok(self, i, case=None, Cm=None, V=None):
        c = self.cert
        return AC.caseOK(c['p'], c['J'], c['em'], self.Nq, c['V'] if V is None else V,
                         c['Cm'][i] if Cm is None else Cm, self.bases[i], case or c['cases'][i])

    def test_accepted(self):
        for i in range(3):
            self.assertEqual(self._ok(i), [])
        self.assertEqual(max(r['H_reduced'] for r in self.cert['report']), D72['H_bound'])

    def test_brackets(self):
        P, Q = self.args[0], self.args[1]
        lo, hi = self.cert['lo'], self.cert['hi']
        for l in range(3):
            self.assertLess(AC.cub(P, Q, lo[l]) * AC.cub(P, Q, hi[l]), 0)
        self.assertTrue(hi[0] < lo[1] and hi[1] < lo[2])

    def test_precision_margin(self):
        for r in self.cert['report']:
            self.assertGreater(r['precision_margin_bits'], 30)

    def test_rejects_larger_matveev_constant(self):
        # the same M₀ with 4 Cm: the cutoff check (index 41) fails
        self.assertIn(41, self._ok(0, Cm=4 * self.cert["Cm"][0]))

    def test_rejects_lower_first_bound(self):
        c = dict(self.cert['cases'][1], M0=self.cert['cases'][1]['M0'] // 2)
        self.assertNotEqual(self._ok(1, case=c), [])

    def test_rejects_narrowed_enclosure(self):
        c = dict(self.cert['cases'][2])
        c['kl'] = c['ku']
        self.assertIn(42, self._ok(2, case=c))
        c = dict(self.cert['cases'][2], Au=self.cert['cases'][2]['Au'] / 2)
        self.assertIn(47, self._ok(2, case=c))
        c = dict(self.cert['cases'][2], cl=self.cert['cases'][2]['cl'] * 2)
        self.assertIn(46, self._ok(2, case=c))

    def test_rejects_small_V(self):
        # V = 0 is too small for 2 K₁ ≤ (V + 1)³ in some case of D = 72
        self.assertTrue(any(35 in self._ok(i, V=0) for i in range(3)))

    def test_receipt_matches(self):
        rec = json.loads((ROOT / 'receipts' / 'analytic_certificates.json').read_text())
        row = next(r for r in rec['classes'] if r['class'].startswith('D = 72'))
        self.assertEqual(row['Cm'], [int(x) for x in self.cert['Cm']])
        self.assertEqual([c['M0'] for c in row['cases']], [c['M0'] for c in self.cert['cases']])


if __name__ == '__main__':
    unittest.main()
