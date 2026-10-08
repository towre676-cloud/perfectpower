import json
import unittest
from fractions import Fraction
from pathlib import Path

from flint import arb, arb_poly, ctx
from perfectpower import wall_stability_certified as wsc
from perfectpower.wall_profile_intervals import ball

ROOT = Path(__file__).resolve().parents[2]
SEED = ROOT/'receipts/flavor_cosmology/wall_profile_interval_seed.json'
RECEIPT = ROOT/'receipts/flavor_cosmology/wall_stability_certified.json'


class Identities(unittest.TestCase):
    def test_symbolic_identities(self):
        out = wsc.exact_identities()
        self.assertTrue(all(v == '0' for v in out.values()))
        self.assertIn('AdA_is_kink_operator', out)

    def test_taylor_cell_gap_encloses_tanh(self):
        old = ctx.prec; ctx.prec = 128
        try:
            x0, dx = ball(Fraction(3, 10)), ball(Fraction(1, 50))
            xm = x0 + dx/2
            # cubic Taylor polynomial of tanh about the left end, in t
            t0 = x0.tanh(); s0 = x0.sech()**2
            p = arb_poly([t0, s0*dx, -s0*t0*dx*dx])
            g = wsc._cell_taylor_gap(p, xm.tanh(), xm.sech()**2, dx, wsc.TANH_SECOND_MAX)
            for k in range(11):
                t = ball(Fraction(k, 10))
                self.assertTrue(abs(p(t) - (x0 + dx*t).tanh()) < g)
        finally:
            ctx.prec = old


class Certificate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.seed = json.loads(SEED.read_text())
        cls.cert = wsc.certify_gap(cls.seed)

    def test_gap_positive_and_below_essential_edge(self):
        b = self.cert['bounds_display_float']
        self.assertGreater(b['gamma_lower'], 1.98)
        self.assertLess(b['gamma_lower'], b['essential_edge_upper'])
        self.assertGreater(b['gamma_over_edge_lower'], .998)
        self.assertGreater(b['gap_GeV_lower'], 125.3)
        self.assertLess(b['gap_GeV_lower'], b['Higgs_threshold_GeV'])
        self.assertTrue(self.cert['kernel_is_translation_only_certified'])

    def test_receipt_replays(self):
        rec = json.loads(RECEIPT.read_text())
        self.assertEqual(rec['certificate_160_bits']['bounds_Arb'], self.cert['bounds_Arb'])
        self.assertTrue(arb(rec['replay_192_bits_gamma_lower']).overlaps(arb(self.cert['bounds_Arb']['gamma_lower'])))

    def test_bad_splitting_rejected(self):
        with self.assertRaises(ArithmeticError):
            wsc.certify_gap(self.seed, tau='0.999')

    def test_damaged_seed_rejected(self):
        bad = json.loads(json.dumps(self.seed))
        j = len(bad['values_hex'])//8
        bad['values_hex'][j][0] = (float.fromhex(bad['values_hex'][j][0]) + 1e-3).hex()
        with self.assertRaises(ArithmeticError):
            wsc.certify_gap(bad)


if __name__ == '__main__':
    unittest.main()
