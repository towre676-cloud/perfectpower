from dataclasses import replace
import unittest
import numpy as np
from scipy.integrate import quad
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall
from perfectpower.wall_gauge_channels import exact_channel_identities,candidate_channel_solution,analyze_channels


class WallGaugeChannels(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.solution=candidate_channel_solution(WallModel(30000,.1,.025,300000,3000),HiggsWall())
        cls.r=analyze_channels(cls.solution)

    def test_exact_full_doublet_and_kinetic_channel_algebra(self):
        checks=exact_channel_identities()
        self.assertEqual(len(checks),24);self.assertTrue(all(v=='0' for v in checks.values()))

    def test_cubic_Ward_moment_is_nonzero_and_independently_reproduced(self):
        r=self.r
        self.assertGreater(r['global_Goldstone_zero_energy_pair_overlap_GeV_half'],.003)
        self.assertLess(r['global_Goldstone_Ward_relative_error'],1e-8)
        self.assertLess(abs(r['global_Goldstone_Ward_boundary_term']),1e-9)

    def test_fixed_inputs_close_on_shell_vector_pairs(self):
        r=self.r
        self.assertFalse(r['bulk_WW_pair_open']);self.assertFalse(r['bulk_ZZ_pair_open'])
        self.assertGreater(r['mass_GeV'],154);self.assertLess(r['mass_GeV'],155)
        self.assertAlmostEqual(r['two_W_threshold_GeV'],159.9,places=10)
        self.assertGreater(r['two_Z_threshold_GeV'],182)

    def test_cubic_vector_vertices_exist_even_with_closed_thresholds(self):
        self.assertGreater(self.r['W_mass_vertex_integrated_form_factor_GeV_half'],.001)
        self.assertGreater(self.r['Z_mass_vertex_integrated_form_factor_GeV_half'],.002)

    def test_profile_supports_barrier_without_asserting_interval_proof(self):
        r=self.r;self.assertTrue(r['sampled_profile_supports_positive_Higgs_barrier'])
        self.assertGreaterEqual(r['minimum_sampled_Higgs_ratio_to_vacuum'],1-1e-10)
        self.assertLess(min(r['profile']['global_Goldstone_potential_over_v2']),0)
        # A negative local Goldstone mass entry does not defeat factorization.
        self.assertLess(abs(r['open_endpoint_derivative_over_x']),1e-8)

    def test_longitudinal_quadratic_form_bound_with_negative_local_well(self):
        def values(z):
            s=1/np.cosh(z);t=np.tanh(z);h=1+.3*s*s
            hp=-.6*s*s*t;hpp=1.2*s*s*t*t-.6*s**4
            a=hp/h;potential=.01*h*h+2*a*a-hpp/h
            f=np.exp(-z*z/8);fp=-z*f/4
            return h,a,potential,f,fp
        direct=quad(lambda z:values(z)[4]**2+values(z)[2]*values(z)[3]**2,-20,20,epsabs=1e-12)[0]
        factored=quad(lambda z:(values(z)[4]+values(z)[1]*values(z)[3])**2+.01*values(z)[0]**2*values(z)[3]**2,-20,20,epsabs=1e-12)[0]
        norm=quad(lambda z:values(z)[3]**2,-20,20)[0]
        self.assertLess(abs(direct-factored),1e-11);self.assertGreater(direct,.01*norm)
        self.assertLess(min(values(z)[2] for z in np.linspace(-5,5,101)),.01)

    def test_gauge_thresholds_and_vertices_depend_on_declared_inputs(self):
        lower=analyze_channels(self.solution,g=.4)
        self.assertTrue(lower['bulk_WW_pair_open']);self.assertTrue(lower['bulk_ZZ_pair_open'])
        self.assertAlmostEqual(lower['W_mass_vertex_integrated_form_factor_GeV_half']/self.r['W_mass_vertex_integrated_form_factor_GeV_half'],(.4/.65)**2,places=12)

    def test_dimensionful_normalization_scaling(self):
        s=dict(self.solution);w=dict(s['wall']);m=w['model'];b=w['bath']
        w['model']=replace(m,v_GeV=4*m.v_GeV,heavy_mass_GeV=4*m.heavy_mass_GeV,current_g_GeV=4*m.current_g_GeV)
        w['bath']=replace(b,v_GeV=4*b.v_GeV);s['wall']=w
        r=analyze_channels(s)
        self.assertAlmostEqual(r['mass_GeV']/self.r['mass_GeV'],4,places=12)
        self.assertAlmostEqual(r['global_Goldstone_zero_energy_pair_overlap_GeV_half']/self.r['global_Goldstone_zero_energy_pair_overlap_GeV_half'],2,places=12)

    def test_domain_convergence_of_integrated_vertex(self):
        shorter=analyze_channels(candidate_channel_solution(WallModel(30000,.1,.025,300000,3000),HiggsWall(),length=18))
        self.assertLess(abs(shorter['global_Goldstone_zero_energy_pair_overlap_GeV_half']/self.r['global_Goldstone_zero_energy_pair_overlap_GeV_half']-1),2e-6)
        self.assertLess(shorter['global_Goldstone_Ward_relative_error'],1e-8)

    def test_invalid_gauge_inputs_rejected(self):
        for g,gp in [(0,.36),(.65,0),(float('nan'),.36)]:
            with self.assertRaises(ValueError):analyze_channels(self.solution,g=g,gprime=gp)

if __name__=='__main__':unittest.main()
