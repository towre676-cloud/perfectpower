import json
import unittest
from math import pi, sqrt, log
from pathlib import Path

import numpy as np
from perfectpower import wall_nucleation_corrections as wc
from perfectpower import wall_two_loop_thermal as w2

ROOT = Path(__file__).resolve().parents[2]
RECEIPT = ROOT/'receipts/flavor_cosmology/wall_two_loop_thermal.json'
VALIDATION = ROOT/'receipts/flavor_cosmology/wall_two_loop_thermal_validation.json'
LAM, V = 0.1, 30000.


class ThermalIntegrals(unittest.TestCase):
    def test_matsubara_decomposition(self):
        brute, formula = w2.matsubara_sunset_check(1.3, 0.7, 1.1, N=1500)
        self.assertLess(abs(brute/formula - 1), 1e-9)

    def test_contour_matches_independent_JB_and_series(self):
        for y in (-5., 4.):
            self.assertAlmostEqual(w2.J_B(y).real, wc.re_JB(y), places=9)
        for y in (-2., 2.):
            a, b = w2.J_B(y), w2.J_B_highT(y)
            self.assertLess(abs(a - b), 1e-9)
        # Im part of the y<0 continuation: pi|y|^{3/2}/6 - pi y^2/32 + O(y^3)
        y = -0.01
        self.assertAlmostEqual(w2.J_B(y).imag, pi*0.001/6 - pi*1e-4/32, delta=1e-7)
        self.assertAlmostEqual(w2.i_T(0.).real, 1/12, places=10)
        self.assertAlmostEqual(w2.i_T(4.).real, wc.tadpole_i(4.)/(2*pi*pi), places=10)

    def test_sunset_angular_integration_and_small_mass_limit(self):
        for y in (-2., 2.):
            self.assertLess(abs(w2.h_2(y) - w2.h_2_direct(y)), 1e-10)
        val = w2.h_2(1e-6).real + 0.25*log(1e-6)*w2.KAPPA
        self.assertLess(abs(val - w2.H2_SMALL_M_CONST), 1.5e-4)
        self.assertAlmostEqual(w2.C_SUN, -3.98413914196581, places=12)

    def test_parwani_no_double_counting(self):
        self.assertLess(abs(w2.parwani_linear_coefficient(1e-3, 0.6)), 1e-6)
        self.assertAlmostEqual(w2.parwani_linear_coefficient(1e-3, 0.6, resummed=False), -0.6/(192*pi), delta=2e-6)


class Scheme(unittest.TestCase):
    def test_on_shell_conditions_and_mu_independence(self):
        phi = np.linspace(-1.2, 1.2, 13)*V
        p0 = [w2.TwoLoopPotential(LAM, V, 0., mu=m) for m in (2000., sqrt(0.2)*V, 30000.)]
        a = [p.os_loops(phi) - p.os_loops(phi)[6] for p in p0]
        for x in a[1:]:
            self.assertLess(np.max(abs(x - a[0])), 1.)       # GeV^4, against loops of order 1e14
        f = lambda t: float(p0[1].delta(np.array([t]))[0])
        h = 1.
        self.assertLess(abs((f(V + h) - f(V - h))/(2*h)), 1e-3)
        self.assertLess(abs((f(V + h) - 2*f(V) + f(V - h))/h**2), 1e-2)
        T = 2999.
        tab = w2.ThermalTables(-LAM*V*V/T**2*1.02, LAM*(3*(1.25*V)**2 - V*V)/T**2, dt=0.12)
        pt = [w2.TwoLoopPotential(LAM, V, T, tables=tab, mu=m) for m in (sqrt(0.2)*V/2, sqrt(0.2)*V*2)]
        a = [p.os_loops(phi) - p.os_loops(phi)[6] for p in pt]
        self.assertLess(np.max(abs(a[1] - a[0])), 1.)
        # one-loop matched MS-bar spread is far below the tree-matched one-loop spread
        ms = [p.msbar_loops(phi) - p.os_loops(phi) for p in pt]
        one = [p.one_loop_msbar_minus_os(phi) for p in pt]
        sp2 = np.ptp((ms[1] - ms[1][6]) - (ms[0] - ms[0][6]))
        sp1 = np.ptp((one[1] - one[1][6]) - (one[0] - one[0][6]))
        self.assertLess(sp2, 0.05*sp1)


class Receipts(unittest.TestCase):
    def test_validation_receipt(self):
        r = json.loads(VALIDATION.read_text())
        self.assertLess(r['matsubara_decomposition']['relative_difference'], 1e-10)
        for row in r['scheme']:
            self.assertLess(row['OS_two_loop_max_mu_dependence_GeV4'], 1.)
            self.assertLess(row['MSbar_two_loop_one_loop_matched_mu_spread_GeV4'],
                            0.05*row['MSbar_one_loop_tree_matched_mu_spread_GeV4'])

    def test_results_receipt(self):
        r = json.loads(RECEIPT.read_text())
        rows = {row['T_GeV']: row for row in r['rows']}
        for T in (1000., 2000., 2999.):
            x = rows[T]['d3']
            self.assertEqual(x['two_loop_method'], 'bounce')
            lo, hi = x['eps_star_total_band']
            self.assertLess(lo, x['eps_star_two_loop'])
            self.assertLess(x['eps_star_two_loop'], hi)
            self.assertLess(abs(x['eps_star_shift_vs_one_loop']), 2e-3)
            self.assertLess(abs(x['virial_defect']), 1e-6)
        for b in r['nucleation_temperature_benchmarks']['rows']:
            lo, hi = b['T_n_two_loop_total_band_GeV']
            self.assertLessEqual(lo, b['T_n_two_loop_GeV'])
            self.assertLessEqual(b['T_n_two_loop_GeV'], hi)


if __name__ == '__main__':
    unittest.main()
