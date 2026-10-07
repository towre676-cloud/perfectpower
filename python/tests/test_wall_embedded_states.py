from dataclasses import replace
import unittest
import numpy as np
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall,solve_coupled_wall
from perfectpower.wall_embedded_states import leading_node_shift,independent_green_node_shift,localized_embedded_candidate
from perfectpower.wall_scattering import outgoing_shape_pole


class RetunedWallNodes(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.slope=leading_node_shift()['threshold_shift_per_portal']
        cls.model=WallModel(1,.1,.025,10,0)
        cls.bath=HiggsWall(portal=.001,lam=.05,v_GeV=1)
        cls.candidate=localized_embedded_candidate(cls.model,cls.bath)

    def test_independent_Green_convolution_and_radius(self):
        direct=independent_green_node_shift()['threshold_shift_per_portal']
        self.assertAlmostEqual(direct,self.slope,places=10)
        shorter=leading_node_shift(radius_x=18)['threshold_shift_per_portal']
        self.assertAlmostEqual(shorter,self.slope,places=10)
        self.assertAlmostEqual(self.slope,-1.36468352107739,places=10)

    def test_joint_mode_is_inside_continuum_with_closed_source(self):
        r=self.candidate;thresholds=r['thresholds_over_v2'];E=r['energy_over_v2']
        self.assertLess(thresholds[0],E);self.assertLess(E,thresholds[1])
        self.assertLess(abs(r['open_channel_endpoint_value']),1e-15)
        self.assertLess(abs(r['open_channel_endpoint_derivative']),1e-15)
        self.assertLess(r['constant_exterior_closed_tail_norm_fraction'],1e-12)
        self.assertLess(r['boundary_residual'],1e-12)
        self.assertGreater(r['full_line_mode_norm_with_unit_source_derivative'],0)

    def test_candidate_quartic_converges_with_domain_and_tolerance(self):
        refined=localized_embedded_candidate(self.model,self.bath,length=22,tol=1e-10)
        self.assertLess(abs(refined['tuned_Higgs_lambda']-self.candidate['tuned_Higgs_lambda']),2e-12)
        self.assertLess(abs(refined['energy_over_v2']-self.candidate['energy_over_v2']),2e-12)
        self.assertLess(refined['closed_channel_endpoint_norm'],self.candidate['closed_channel_endpoint_norm']/40)

    def test_derived_slope_is_not_fitted_to_the_full_candidate(self):
        r=localized_embedded_candidate(self.model,replace(self.bath,portal=1e-5))
        actual=r['threshold_shift_from_scalar_node']/1e-5
        self.assertLess(abs(actual-self.slope),.006)
        self.assertGreater(abs(actual-self.slope),1e-5)

    def test_first_order_correction_gives_sixth_power_width(self):
        widths=[]
        for kap in [1e-4,2e-4]:
            b=HiggsWall(portal=kap,lam=(.1+self.slope*kap)/2,v_GeV=1)
            w=solve_coupled_wall(self.model,b,length_factor=18)
            widths.append(outgoing_shape_pole(w,tol=1e-10)['width_GeV'])
        self.assertGreater(widths[0],0)
        self.assertGreater(widths[1]/widths[0],62);self.assertLess(widths[1]/widths[0],66)

    def test_independent_outgoing_solve_and_detuning(self):
        H=self.candidate['tuned_Higgs_lambda'];widths=[]
        for relative in [-.001,0,.001]:
            b=replace(self.bath,lam=H*(1+relative));w=solve_coupled_wall(self.model,b,length_factor=18)
            p=outgoing_shape_pole(w,tol=1e-10,energy_guess=self.candidate['energy_over_v2'])
            widths.append(p['width_GeV'])
            if not relative:self.assertLess(abs(p['energy_over_v2'][0]-self.candidate['energy_over_v2']),2e-12)
        self.assertGreater(widths[0],1e-10);self.assertGreater(widths[2],1e-10)
        # Absolute zero is not inferred from this numerical comparison.
        self.assertLess(abs(widths[1]),min(widths[0],widths[2])*1e-10)

    def test_retune_source_keeps_declared_Higgs_parameters(self):
        m=WallModel(30000,.1,.025,300000,3000);b=HiggsWall()
        r=localized_embedded_candidate(m,b,tune='source_lambda',tol=1e-10)
        self.assertEqual(r['tuned_Higgs_lambda'],b.lam)
        self.assertAlmostEqual(r['tuned_source_lambda'],1.7618816494787e-5,places=15)
        self.assertGreater(r['mass_GeV'],154);self.assertLess(r['mass_GeV'],155)
        self.assertLess(abs(r['open_channel_endpoint_value']),1e-15)
        self.assertEqual(m.lam,.1) # Input model was not mutated.

    def test_guards_static_action_and_controls(self):
        with self.assertRaises(ValueError):localized_embedded_candidate(self.model,replace(self.bath,portal=0))
        with self.assertRaises(ValueError):localized_embedded_candidate(self.model,self.bath,tune='bad')
        with self.assertRaises(ValueError):localized_embedded_candidate(self.model,self.bath,length=3)
        with self.assertRaises(ValueError):leading_node_shift(radius_x=3)


if __name__=='__main__':unittest.main()
