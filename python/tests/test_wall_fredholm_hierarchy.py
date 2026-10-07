from dataclasses import replace
import unittest
import numpy as np
from perfectpower.wall_fredholm_hierarchy import universal_responses,retuning_coefficients,threshold_series,exact_hierarchy_identities
from perfectpower.wall_embedded_states import independent_green_node_shift,localized_embedded_candidate
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall,solve_coupled_wall
from perfectpower.wall_scattering import outgoing_shape_pole


class WallFredholmHierarchy(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.r=universal_responses()

    def test_exact_force_coefficients_and_order_bookkeeping(self):
        checks=exact_hierarchy_identities()
        self.assertEqual(len(checks),15)
        self.assertTrue(all(v=='0' for v in checks.values()))

    def test_independent_cosine_and_closed_Fredholm_moments(self):
        r=self.r
        direct=independent_green_node_shift()['threshold_shift_per_portal']
        self.assertLess(abs(r['linear_threshold_coefficient']-direct),2e-12)
        self.assertLess(abs(r['linear_threshold_coefficient']-r['independent_cosine_linear_coefficient']),2e-12)
        self.assertLess(abs(r['shape_energy_coefficient']-r['independent_Fredholm_energy_coefficient']),2e-10)

    def test_response_domain_convergence(self):
        shorter=universal_responses(radius_x=28)
        for key in ['quadratic_Higgs_coefficient','quadratic_source_coefficient','shape_energy_coefficient']:
            self.assertLess(abs(shorter[key]-self.r[key]),5e-10)

    def test_forced_equations_at_independent_interior_points(self):
        q=np.array([.13,.41,1.17,2.65,4.1]);r=self.r;sol=r['solutions'];s=1/np.cosh(q);u=np.tanh(q);p=s*u
        H,A,T,B,W=[sol[n].sol(q)[0] for n in ['H','A','T','B','W']]
        C=r['linear_threshold_coefficient'];e=r['shape_energy_coefficient']
        expected={'H':2*H-s*s,'A':(4-6*s*s)*A+u*(2*H-s*s),
            'T':2*T+3*H*H+C*H-H*s*s,
            'B':-B+s*((8-2*s*s)*H+C-s*s),
            'W':(1-6*s*s)*W+(12*u*A+2*H+3*u*u-1-e)*p+2*u*s}
        for n,force in expected.items():
            np.testing.assert_allclose(sol[n].sol(q,1)[1],force,atol=2e-8,rtol=2e-8)

    def test_parity_normalization_and_decaying_responses(self):
        r=self.r;sol=r['solutions']
        for n in ['H','T','B']:self.assertLess(abs(sol[n].sol(0)[1]),1e-12)
        for n in ['A','W']:self.assertLess(abs(sol[n].sol(0)[0]),1e-12)
        self.assertLess(abs(sol['W'].sol(0)[1]),1e-12)
        for n in sol:self.assertLess(abs(sol[n].sol(20)[0]),2e-7)

    def test_predicts_independent_nonlinear_threshold_and_energy(self):
        for lam,h0 in [(.1,1),(.2,.5),(.07,1.5)]:
            coeff=retuning_coefficients(lam,h0,responses=self.r);errors=[]
            for kap in [1e-4,2e-4]:
                result=localized_embedded_candidate(WallModel(1,lam,.025,10,0),HiggsWall(portal=kap,lam=lam/(2*h0*h0),v_GeV=h0),length=22,tol=1e-10)
                Q=(result['threshold_shift_from_scalar_node']-coeff['linear_threshold_coefficient']*kap)/kap**2
                energy=(result['energy_over_v2']-1.5*lam)/kap**2
                errors.append(abs(Q-coeff['quadratic_threshold_coefficient']))
                self.assertLess(abs(energy/coeff['quadratic_shape_energy_coefficient']-1),.001)
                self.assertLess(errors[-1]/abs(coeff['quadratic_threshold_coefficient']),.001)
            self.assertLess(errors[0],errors[1]*.65)

    def test_quadratic_retuning_restores_eighth_power_width(self):
        widths=[]
        for kap in [.000125,.00025]:
            pred=threshold_series(kap,.1,1,responses=self.r)
            wall=solve_coupled_wall(WallModel(1,.1,.025,10,0),HiggsWall(portal=kap,lam=pred['Higgs_lambda_through_quadratic'],v_GeV=1),length_factor=22)
            pole=outgoing_shape_pole(wall,tol=1e-11,energy_guess=pred['shape_energy_through_quadratic'])
            self.assertGreater(pole['width_GeV'],0)
            self.assertLess(pole['current_identity_relative_error'],1e-3)
            widths.append(pole['width_GeV'])
        ratio=widths[1]/widths[0]
        self.assertGreater(ratio,250);self.assertLess(ratio,275)

    def test_symbolic_scaling_across_parameter_changes(self):
        a=retuning_coefficients(.1,1,responses=self.r);b=retuning_coefficients(.2,1,responses=self.r)
        self.assertEqual(a['linear_threshold_coefficient'],b['linear_threshold_coefficient'])
        self.assertEqual(a['quadratic_threshold_coefficient'],2*b['quadratic_threshold_coefficient'])
        self.assertEqual(a['quadratic_shape_energy_coefficient'],2*b['quadratic_shape_energy_coefficient'])

    def test_nonfinite_and_invalid_controls_are_rejected(self):
        for lam,h in [(0,1),(.1,0),(float('nan'),1),(.1,float('inf'))]:
            with self.assertRaises(ValueError):retuning_coefficients(lam,h,responses=self.r)
        for radius,tol in [(3,1e-10),(24,0),(float('inf'),1e-10),(24,float('nan'))]:
            with self.assertRaises(ValueError):universal_responses(radius_x=radius,tol=tol)
        with self.assertRaises(ValueError):threshold_series(float('nan'),.1,1,responses=self.r)

if __name__=='__main__':unittest.main()
