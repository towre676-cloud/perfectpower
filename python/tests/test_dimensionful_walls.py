from dataclasses import replace
from fractions import Fraction as Q
from math import sqrt,pi
import json
import unittest
import numpy as np
from scipy.integrate import quad
from perfectpower.dimensionful_walls import *


class DimensionfulWalls(unittest.TestCase):
    def setUp(self):self.model=WallModel(30000.,.1,.025,300000.,3000.)

    def test_dimensionful_rescaling(self):
        a=tension_bounds(self.model)
        b=tension_bounds(WallModel(300000.,.1,.025,3000000.,30000.))
        self.assertAlmostEqual(b['lower_GeV3']/a['lower_GeV3'],1000.)
        self.assertEqual(a['exact_trial_relative_excess'],b['exact_trial_relative_excess'])

    def test_independent_kink_energy_and_heavy_kinetic_integral(self):
        lam=.1;alpha=.1;mu=10.;k=sqrt(lam/2)
        def density(r):
            u=np.tanh(k*r);du=k*(1-u*u);dS=-2*alpha*u*du/mu**2
            return .5*(du*du+dS*dS)+lam*(u*u-1)**2/4
        energy=quad(density,-100,100,epsabs=1e-12)[0]
        bound=tension_bounds(self.model)['upper_GeV3']/self.model.v_GeV**3
        self.assertAlmostEqual(energy,bound,places=11)

    def test_full_wall_satisfies_analytic_sandwich_and_first_integral(self):
        r=solve_wall(self.model)
        self.assertGreaterEqual(r['tension_GeV3'],r['analytic_bounds']['lower_GeV3'])
        self.assertLessEqual(r['tension_GeV3'],r['analytic_bounds']['upper_GeV3'])
        self.assertLess(r['first_integral_maximum_error'],1e-9)
        self.assertLess(r['boundary_residual'],1e-12)

    def test_bias_absent_near_transition_and_thermal_restoration(self):
        m=replace(self.model,bias_h0_GeV3=1e-12,bias_onset_GeV=3000.)
        self.assertEqual(m.h(m.critical_temperature_GeV),0)
        self.assertEqual(m.h(3000.),0)
        high=thermal_vacua(m,2*m.critical_temperature_GeV)
        self.assertFalse(high['two_local_minima'])
        self.assertEqual(float(high['stationary_points'][0]['phi_GeV']),0)

    def test_tiny_bias_energy_gap_without_float_cancellation(self):
        m=replace(self.model,bias_h0_GeV3=1e-13,bias_onset_GeV=3000.)
        r=thermal_vacua(m,.03)
        gap=float(r['exact_numeric_energy_gap_GeV4'])
        expected=2*m.h(.03)*m.v_GeV*sqrt(1-(.03/m.critical_temperature_GeV)**2)
        self.assertTrue(r['two_local_minima']);self.assertAlmostEqual(gap/expected,1.,places=12)

    def test_radiation_units_and_inverse(self):
        H=radiation_H(.03,10.75)
        self.assertAlmostEqual(radiation_T(H,10.75),.03,places=14)
        self.assertGreater(HBAR_GEV_S/(2*H),.0008)
        self.assertLess(HBAR_GEV_S/(2*H),.0009)

    def test_scaling_annihilation_balance(self):
        sigma=tension_bounds(self.model)['lower_GeV3'];H=radiation_H(.03,10.75)
        m=replace(self.model,bias_h0_GeV3=2*3*.8*sigma*H/(2*self.model.v_GeV),bias_onset_GeV=3000.)
        a=annihilation(m,sigma)
        self.assertAlmostEqual(a['temperature_GeV'],.03,places=10)
        self.assertAlmostEqual(a['bias_gap_GeV4']/(2*3*.8*sigma*a['H_GeV']),1.,places=12)

    def test_Higgs_decay_channel_and_extra_trial_cost(self):
        b=Higgs_bath_completion(self.model);m=b['source_mass_GeV'];mu=2e-7*self.model.v_GeV
        expected=mu*mu/(32*pi*m)*sqrt(1-4*b['Higgs_mass_GeV']**2/m**2)
        self.assertAlmostEqual(expected/b['leading_phi_to_hh_width_GeV'],1.,places=13)
        self.assertEqual(Q(b['exact_source_kink_relative_potential_cost']),Q('0.0000001')**2/(2*Q('.13')*Q('.1')))
        self.assertGreater(b['Higgs_curvature_at_CP_transition_GeV2'],0)
        self.assertLess(b['lifetime_seconds'],1e-12)

    def test_delay_and_redshift_scaling(self):
        sigma=8e12;H=radiation_H(.03,10.75)
        a=gw_estimate(sigma,H);b=gw_estimate(sigma,H,emission_H_ratio=.1,peak_frequency_in_H=2.)
        self.assertAlmostEqual(b['peak_Omega_h2']/a['peak_Omega_h2'],100.)
        self.assertAlmostEqual(b['peak_frequency_Hz']/a['peak_frequency_Hz'],2*sqrt(.1))

    def test_spectral_continuity_and_slopes(self):
        x=np.array([.01,.1,1.,10.,100.]);s=spectrum_shape(x,middle_slope=-.5,uv_slope=-1.8)
        self.assertAlmostEqual(s[1]/s[0],1000.)
        self.assertAlmostEqual(s[3]/s[2],10**(-.5))
        self.assertAlmostEqual(s[4]/s[3],10**(-1.8))

    def test_integrated_template_against_independent_quadrature(self):
        g=gw_estimate(8e12,1e-21,middle_slope=-.5,uv_slope=-1.8)
        shape_integral=sum(quad(lambda logx:float(spectrum_shape(np.exp(logx),middle_slope=-.5,uv_slope=-1.8)),a,b)[0] for a,b in [(-50,0),(0,np.log(10)),(np.log(10),50)])
        self.assertAlmostEqual(g['integrated_Omega_h2']/g['peak_Omega_h2'],shape_integral,places=10)

    def test_flat_UV_cap_and_invalid_inputs(self):
        g=gw_estimate(8e12,1e-21,wall_inverse_width_GeV=1000.)
        self.assertGreater(g['integrated_flat_UV_cap_Omega_h2'],g['integrated_Omega_h2'])
        with self.assertRaises(ValueError):gw_estimate(8e12,1e-21,emission_H_ratio=2)
        with self.assertRaises(ValueError):WallModel(-1,.1,.1,1,0)
        with self.assertRaises(ValueError):replace(self.model,bias_h0_GeV3=1,bias_onset_GeV=100000.)

    def test_published_screen_and_flavor_limit(self):
        from develop_dimensionful_walls import ROOT
        r=json.loads((ROOT/'receipts/flavor_cosmology/dimensionful_walls.json').read_text())
        self.assertTrue(all(r['screen_results'].values()))
        self.assertEqual(r['nuisance_scan_summary']['points'],162)
        self.assertEqual(r['nuisance_scan_summary']['passes'],162)
        self.assertFalse(r['published_nonet_flavor_branch']['CP_breaking_global_vacua'])
        self.assertGreater(r['declared_bath_completion']['leading_phi_to_hh_width_GeV']/r['annihilation']['H_GeV'],1e9)


if __name__=='__main__':unittest.main()
