import unittest
try:
 import numpy as np
 import scipy
except ImportError:raise unittest.SkipTest('optional cooling tests require NumPy/SciPy')
from perfectpower.wall_cooling import *

class ThermalWalls(unittest.TestCase):
 def test_ordered_transitions_and_continuous_bulk_branches(self):
  p=CoolingInputs();tr=transitions(p);b=tr['bulk_Higgs_ordering_temperature_GeV']
  self.assertLess(b,tr['reduced_kink_wall_Higgs_onset_GeV'])
  self.assertLess(tr['reduced_kink_wall_Higgs_onset_GeV'],tr['source_ordering_temperature_GeV'])
  a=bulk_vacuum(b-1e-7);c=bulk_vacuum(b+1e-7)
  self.assertLess(abs(a['u']-c['u']),1e-8);self.assertLess(a['h'],1e-5);self.assertEqual(c['h'],0)
 def test_excess_potential_nonnegative_global_minimum(self):
  p=CoolingInputs();rng=np.random.default_rng(9)
  for T in [0,100,140.27,600,900]:
   b=bulk_vacuum(T);self.assertAlmostEqual(excess_potential(b['u'],b['y'],b['h'],T),0)
   u=rng.normal(size=1000);y=rng.normal(size=1000)*.001;h=rng.normal(size=1000)*.02
   self.assertGreaterEqual(float(np.min(excess_potential(u,y,h,T))),0)
 def test_PT_onset_has_zero_analytic_eigenvalue(self):
  p=CoolingInputs();T=transitions(p)['reduced_kink_wall_Higgs_onset_GeV']
  self.assertLess(abs(projected_condensation(T,p)['PT_ground_eigenvalue_GeV2']),1e-9)
 def test_canonical_source_wall_and_Riccati_sign_change(self):
  p=CoolingInputs();tr=transitions(p);T=tr['reduced_kink_wall_Higgs_onset_GeV'];w=source_wall(T)
  self.assertLess(w['BVP_residual'],3e-10)
  self.assertGreater(Higgs_zero_mode_match(T-.001),0)
  self.assertLess(Higgs_zero_mode_match(T+.001),0)
 def test_portal_zero_removes_wall_only_transition(self):
  from dataclasses import replace
  p=replace(CoolingInputs(),kappa=0)
  t=transitions(p);self.assertAlmostEqual(t['bulk_Higgs_ordering_temperature_GeV'],t['reduced_kink_wall_Higgs_onset_GeV'])
 def test_restored_profile_has_no_vector_tree_defect(self):
  w=solve_thermal_wall(600)
  self.assertEqual(w['report']['central_Higgs_GeV'],0)
  v=gauge_background(w['report']);self.assertTrue(all(x==0 for x in v['W_tree_mass_squared_GeV2']))
 def test_positive_wall_condensate_has_lower_action(self):
  T=transitions()['bulk_Higgs_ordering_temperature_GeV']+.005
  w=solve_thermal_wall(T)
  self.assertGreater(w['report']['central_Higgs_GeV'],2)
  e=wall_condensation_energy(w);self.assertLess(e['energy_difference_GeV3'],-.6)
  self.assertGreater(w['report']['Higgs_squared_excess_area_GeV'],0)
 def test_Robin_model_improves_nonlinear_energy_reference(self):
  T=transitions()['bulk_Higgs_ordering_temperature_GeV']+.002
  a=robin_defect_condensation(T);self.assertGreater(a['predicted_central_Higgs_GeV'],3)
  self.assertLess(a['predicted_condensation_energy_GeV3'],-2)
 def test_invalid_phases_and_inputs_rejected(self):
  with self.assertRaises(ValueError):CoolingInputs(c=-1)
  with self.assertRaises(ValueError):bulk_vacuum(-1)
  with self.assertRaises(ValueError):solve_thermal_wall(900)
  with self.assertRaises(ValueError):source_wall(0)
if __name__=='__main__':unittest.main()
