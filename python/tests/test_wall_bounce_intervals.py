import json
import unittest
from decimal import Decimal
from fractions import Fraction
from pathlib import Path

from flint import arb
from perfectpower import wall_bounce_intervals as wb

ROOT = Path(__file__).resolve().parents[2]
RECEIPT = ROOT/'receipts/flavor_cosmology/wall_bounce_intervals.json'


class Integrator(unittest.TestCase):
    def test_cubic_o3_bounce_enclosure(self):
        pot = wb.cubic()
        seed, _ = wb.seed_phi0(pot, 3)
        cert = wb.certify_bounce(pot, 3, seed=seed)
        self.assertTrue(cert['certified'])
        self.assertEqual({cert['lo']['status'], cert['hi']['status']}, {'over', 'under'})
        s = cert['s']
        self.assertLess(s.rad(), 1e-8)
        self.assertLess(abs(float(s.mid()) - 43.66023671624), 1e-8)
        C3 = wb.spinodal_constants({3: s})[3]
        self.assertLess(abs(float(C3.mid()) - 62.1484490899), 1e-7)

    def test_wrong_bracket_is_not_certified(self):
        pot = wb.cubic()
        with wb._prec(160):
            seed = arb('4.1916829544425191267766360180409') + wb.exact(Fraction(1, 10**6))
        cert = wb.certify_bounce(pot, 3, seed=seed, delta=Fraction(1, 10**12), u_stop=1e-7)
        self.assertEqual(cert['lo']['status'], cert['hi']['status'])
        self.assertFalse(cert['exists'])

    def test_uniqueness_box_and_energy_bound(self):
        pot = wb.quartic(0.3758661029381119)
        seed = arb(wb._float_phi0(pot, 4))
        ub = wb.certify_unique_box(pot, 4, seed, Fraction(1, 10**8))
        self.assertEqual(ub['status'], 'unique')
        self.assertTrue(ub['phi_R'] < pot.x_infl)
        with wb._prec(160):
            pot.at(160)
            eta, data = wb.near_true_vacuum_eta(pot, 4)
        self.assertTrue(eta > 0)
        self.assertGreater(data['E0_lower'], data['D1_upper'])


class Receipt(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.r = json.loads(RECEIPT.read_text())

    def test_spinodal_constants(self):
        for name, val in (('C3', '62.14844908991'), ('C4', '179.3619745271')):
            c = self.r['spinodal_constants'][name]
            lo, hi = (Decimal(x) for x in c['certified'])
            self.assertLess(lo, Decimal(val) + Decimal('1e-9'))
            self.assertGreater(hi, Decimal(val) - Decimal('1e-9'))
            self.assertLess(hi - lo, Decimal('1e-10'))
            self.assertTrue(c['quoted_value_is_certified_rounding'])

    def test_benchmarks_certified(self):
        rows = self.r['benchmarks']
        self.assertEqual(len(rows), 10)
        for row in rows:
            self.assertTrue(row['certified'])
            self.assertTrue(row['virial_and_direct_overlap'])
            lo, hi = (Decimal(x) for x in row['S_certified'])
            self.assertLess((hi - lo)/lo, Decimal('1e-8'))
            if 'floating_bounce_relative_deviation' in row:
                self.assertLess(abs(row['floating_bounce_relative_deviation']), 1e-7)
        self.assertTrue(self.r['summary']['all_existence_certified'])


if __name__ == '__main__':
    unittest.main()
