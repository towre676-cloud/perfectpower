import unittest
from dataclasses import replace
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall,solve_coupled_wall
from perfectpower.wall_gaussian_fredholm import gaussian_node_response,singlet_resolvent_check,fixed_Higgs_source_prediction,exact_gaussian_portal_identities
from perfectpower.wall_embedded_states import leading_node_shift,localized_embedded_candidate
from perfectpower.wall_scattering import outgoing_shape_pole


class GaussianFredholmNodes(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.model=WallModel(1,.1,.025,3,2)
        cls.response=gaussian_node_response(cls.model)

    def test_exact_coupled_polynomial_and_transversality_identities(self):
        values=exact_gaussian_portal_identities()
        self.assertEqual(len(values),7);self.assertTrue(all(v=='0' for v in values.values()))

    def test_zero_Gaussian_limit_recovers_scalar_node_and_slope(self):
        r=gaussian_node_response(replace(self.model,current_g_GeV=0))
        self.assertLess(abs(r['leading_node_threshold_over_v2']-.1),2e-11)
        self.assertLess(abs(r['shape_energy_over_v2']-.15),2e-11)
        self.assertLess(abs(r['linear_threshold_coefficient']-leading_node_shift()['threshold_shift_per_portal']),2e-10)

    def test_coupled_thresholds_and_independent_cosine_root(self):
        r=self.response
        self.assertLess(r['leading_node_threshold_over_v2'],r['shape_energy_over_v2'])
        self.assertLess(r['shape_energy_over_v2'],r['source_thresholds_over_v2'][0])
        self.assertLess(abs(r['leading_form_factor_at_node']),2e-10)
        self.assertLess(abs(r['open_wave_number_over_k']-r['independent_form_factor_root_over_k']),2e-10)
        self.assertGreater(abs(r['leading_node_shift_from_scalar_threshold']),.002)

    def test_nonzero_Fourier_transversality_and_independent_slope(self):
        r=self.response
        self.assertGreater(r['radiation_transversality_moment'],1.)
        self.assertLess(abs(r['radiation_transversality_moment']-r['independent_transversality_from_form_factor']),2e-9)
        self.assertLess(abs(r['linear_threshold_coefficient']-r['independent_cosine_linear_coefficient']),2e-9)

    def test_heavy_Green_kernel_retains_gradient_response(self):
        r=self.response;check=singlet_resolvent_check(r)
        self.assertLess(check['maximum_absolute_difference'],2e-10)
        # A local valley replacement would give zero here, since u(0)=p(0)=0.
        self.assertLess(r['solutions']['shape'].sol(0)[1],-.001)

    def test_domain_and_Higgs_ratio_independence(self):
        short=gaussian_node_response(self.model,length=28,h0=.4)
        for key in ['leading_node_threshold_over_v2','shape_energy_over_v2','linear_threshold_coefficient']:
            self.assertLess(abs(short[key]-self.response[key]),2e-8)

    def test_independent_nonlinear_slope_approaches_prediction(self):
        errors=[];r=self.response
        for kap in [5e-5,1e-4]:
            b=HiggsWall(portal=kap,lam=r['leading_node_threshold_over_v2']/2,v_GeV=1)
            c=localized_embedded_candidate(self.model,b,length=22,tol=1e-10)
            measured=(2*c['tuned_Higgs_lambda']-r['leading_node_threshold_over_v2'])/kap
            errors.append(abs(measured-r['linear_threshold_coefficient']))
        self.assertLess(errors[0],.004);self.assertLess(errors[0],errors[1]*.55)

    def test_first_coupled_correction_gives_sixth_power_leakage(self):
        r=self.response;widths=[]
        for kap in [1e-4,2e-4]:
            b=HiggsWall(portal=kap,lam=(r['leading_node_threshold_over_v2']+r['linear_threshold_coefficient']*kap)/2,v_GeV=1)
            wall=solve_coupled_wall(self.model,b,length_factor=22)
            p=outgoing_shape_pole(wall,tol=1e-10,energy_guess=r['shape_energy_over_v2'])
            self.assertGreater(p['width_GeV'],0);self.assertLess(p['current_identity_relative_error'],1e-5)
            widths.append(p['width_GeV'])
        self.assertGreater(widths[1]/widths[0],62);self.assertLess(widths[1]/widths[0],66)

    def test_fixed_Higgs_source_prediction_is_independent_of_full_tuning(self):
        model=WallModel(30000,.1,.025,300000,3000);b=HiggsWall()
        pred=fixed_Higgs_source_prediction(model,b)
        c=localized_embedded_candidate(model,b,tune='source_lambda',length=22,tol=1e-10)
        self.assertEqual(pred['fixed_Higgs_lambda'],b.lam)
        self.assertLess(abs(pred['predicted_source_lambda']/c['tuned_source_lambda']-1),4e-6)
        self.assertLess(abs(pred['source_lambda_equation_residual']),1e-15)
        self.assertEqual(model.lam,.1)

    def test_invalid_controls_and_bias_are_rejected(self):
        for kw in [{'h0':0},{'h0':float('nan')},{'length':5},{'tol':0},{'tol':float('nan')}]:
            with self.assertRaises(ValueError):gaussian_node_response(self.model,**kw)
        biased=replace(self.model,bias_h0_GeV3=.001,bias_onset_GeV=.1)
        with self.assertRaises(ValueError):gaussian_node_response(biased)
        with self.assertRaises(ValueError):singlet_resolvent_check(self.response,points=(-1.,))

if __name__=='__main__':unittest.main()
