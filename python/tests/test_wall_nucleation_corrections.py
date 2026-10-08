import json
import unittest
from math import pi
from pathlib import Path

import numpy as np
from perfectpower import wall_nucleation as wn
from perfectpower import wall_nucleation_corrections as wc

ROOT = Path(__file__).resolve().parents[2]
RECEIPT = ROOT/'receipts/flavor_cosmology/wall_nucleation_corrections.json'
LAM = .1


class ThermalFunctions(unittest.TestCase):
    def test_JB_values_and_high_T_expansion(self):
        self.assertAlmostEqual(wc.re_JB(0.), -pi**4/45, places=10)
        y = 1e-2
        approx = -pi**4/45 + pi*pi*y/12 - pi*y**1.5/6
        self.assertLess(abs(wc.re_JB(y) - approx), 2e-4)
        self.assertAlmostEqual(wc.tadpole_i(0.), pi*pi/6, places=10)
        # dJ_B/dy = i(y)/2
        for y in (.5, 3.):
            h = 1e-4
            self.assertAlmostEqual((wc.re_JB(y + h) - wc.re_JB(y - h))/(2*h), wc.tadpole_i(y)/2, places=6)

    def test_negative_y_real_part_is_continuous(self):
        self.assertLess(abs(wc.re_JB(-1e-6) - wc.re_JB(1e-6)), 1e-5)


class Potential(unittest.TestCase):
    def test_on_shell_conditions_and_derivatives(self):
        sp = wc.ThermalSpline(-10., 60., n=121)
        pots = [wc.Corrected(LAM, parts=('cw', 'heavy'), heavy=(1000., .004)),
                wc.Corrected(LAM, r=1.001, tau=.1, parts=('cw', 'heavy', 'thermal1'), heavy=(1000., .004), spline=sp),
                wc.Corrected(LAM, r=1.001, tau=.1, parts=('cw', 'thermal1'), spline=sp, y_shift=LAM/4),
                wc.Corrected(LAM, parts=('cw',), M_IR=.05)]
        h = 1e-6
        x = np.linspace(-1.4, 1.4, 15)
        for p in pots:
            fd = (p.delta(x + h) - p.delta(x - h))/(2*h)
            self.assertLess(np.max(abs(fd - p.ddelta(x))), 1e-6)
            f = p.scalar_dU(.2)
            self.assertLess(max(abs(f(t) - float(p.dU(t, .2))) for t in x), 1e-12)
        p = pots[0]
        one = np.array([1.])
        self.assertLess(abs(p.ddelta(one)[0]), 1e-15)
        self.assertLess(abs((p.ddelta(one + h) - p.ddelta(one - h))[0]/(2*h)), 1e-8)

    def test_spinodal_tree_and_on_shell(self):
        t = wc.corrected_spinodal(wc.Corrected(LAM, parts=()))
        self.assertAlmostEqual(t['eps_sp'], wn.EPS_SPINODAL, places=10)
        self.assertLess(abs(t["C"][3]/wn.spinodal_constant_exact(3) - 1), 1e-5)
        c = wc.corrected_spinodal(wc.Corrected(LAM, parts=('cw',)))
        self.assertLess(c['eps_sp'], wn.EPS_SPINODAL)
        self.assertAlmostEqual(c['eps_sp']/wn.EPS_SPINODAL - 1, -5.57e-3, delta=2e-4)


class Bounces(unittest.TestCase):
    def test_generic_bounce_matches_tree_and_first_order(self):
        tree = wc.Corrected(LAM, parts=())
        b0 = wc.bounce(tree, .37, 4)
        self.assertAlmostEqual(b0['s'], wn.bounce(.37, 4)['s'], places=8)
        cw = wc.Corrected(LAM, parts=('cw',))
        b1 = wc.bounce(cw, .37, 4)
        self.assertLess(abs(b1['virial_defect']), 1e-7)
        first, _ = wc.first_order_shift(b0, cw.delta, 4)
        self.assertLess(abs(first/(b1['s'] - b0['s']) - 1), .03)
        self.assertLess(b1['s'], b0['s'])


class Receipt(unittest.TestCase):
    def test_receipt_structure(self):
        r = json.loads(RECEIPT.read_text())
        self.assertFalse(r['conclusions']['declared_bias_nucleates'])
        self.assertLess(r['zero_temperature']['spinodal_relative_shift_OS'], 0)
        for row in r['rows']:
            for d in ('d3', 'd4'):
                x = row[d]
                if x['corrected_method'] == 'bounce':
                    lo, hi = x['eps_star_corrected_bracket']
                    self.assertLessEqual(lo, x['eps_star_corrected'])
                    self.assertGreaterEqual(hi, x['eps_star_corrected'])
                    self.assertLess(abs(x['virial_defect']), 1e-6)
        for b in r['nucleation_temperature_benchmarks']['rows']:
            if b['T_n_tree_GeV'] and b['T_n_corrected_GeV']:
                self.assertGreater(b['T_n_corrected_GeV'], b['T_n_tree_GeV'])


if __name__ == '__main__':
    unittest.main()
