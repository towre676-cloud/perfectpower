from dataclasses import replace
from fractions import Fraction as Q
from math import pi,sqrt
import unittest
import numpy as np
from perfectpower.dimensionful_walls import WallModel,Higgs_bath_completion
from perfectpower.wall_fluctuations import HiggsWall,solve_coupled_wall,fluctuation_spectrum,potential_and_hessian,scalar_reference
from perfectpower.wall_vacuum_branches import unbiased_global_vacuum,biased_stationary_branches,real_root_intervals,sign_at_root,exact_transition_temperatures_squared
from perfectpower import polyalg as P
from perfectpower.core import evaluate


class ExactWallVacua(unittest.TestCase):
    def setUp(self):
        self.model=WallModel(30000.,.1,.025000033333333335,300000.,3000.)
        self.bath=HiggsWall()

    def test_all_three_unbiased_thermal_phases_and_global_KKT(self):
        for T,faces,count in [(0,['source','Higgs'],2),(100,['source','Higgs'],2),(200,['source'],2),(70000,[],1)]:
            r=unbiased_global_vacuum(self.model,self.bath,T)
            self.assertEqual(r['active_faces'],faces);self.assertEqual(r['CP_global_components'],count)
            self.assertEqual(Q(r['exact_positive_determinant']),Q('0.013'))
            self.assertTrue(all(Q(g)>=0 for g in r['KKT_gradient_twice']))

    def test_zero_temperature_gaussian_and_Higgs_minima(self):
        r=unbiased_global_vacuum(self.model,self.bath,0)
        self.assertEqual(Q(r['squared_source_over_v2']),1)
        self.assertEqual(Q(r['squared_radial_Higgs_over_v2']),Q(246,30000)**2)
        self.assertEqual(Q(r['S_over_v']),Q(-1,1000))

    def test_transition_values_against_independent_thermal_completion(self):
        r=exact_transition_temperatures_squared(self.model,self.bath)
        cp=sqrt(float(Q(r['CP_transition_GeV2'])))
        h=sqrt(float(Q(r['Higgs_transition_GeV2'])))
        self.assertAlmostEqual(cp,Higgs_bath_completion(self.model)['leading_three_field_CP_transition_GeV'],places=8)
        self.assertGreater(h,140);self.assertLess(h,141)
        self.assertEqual(unbiased_global_vacuum(self.model,self.bath,h*.999)['active_faces'],['source','Higgs'])
        self.assertEqual(unbiased_global_vacuum(self.model,self.bath,h*1.001)['active_faces'],['source'])

    def test_cubic_spinodal_and_exact_denominator_zero_branches(self):
        # (t-1)^2(t+2): a double spinodal must not disappear.
        p=P.poly((2,-3,0,1));roots=real_root_intervals(p,bits=60)
        self.assertEqual(len(roots),2)
        self.assertEqual([sign_at_root(p,(-1,1),r) for r in roots],[-1,0])
        self.assertEqual([sign_at_root(p,P.derivative(p),r) for r in roots],[1,0])

    def test_nonrational_root_gcd_and_complete_root_intervals(self):
        p=P.poly((0,-2,0,1));roots=real_root_intervals(p,bits=90)
        self.assertEqual(len(roots),3)
        self.assertEqual([sign_at_root(p,(-2,0,1),r) for r in roots],[0,-1,0])
        for lo,hi in roots:
            self.assertLessEqual(hi-lo,Q(1,2**90))
            if lo!=hi:self.assertLessEqual(evaluate(p,lo)*evaluate(p,hi),0)

    def test_tiny_bias_retains_false_vacuum_and_Higgs_unstable_saddles(self):
        m=replace(self.model,bias_h0_GeV3=2.584366229533845e-13,bias_onset_GeV=3000.)
        r=biased_stationary_branches(m,self.bath,Q(3,100))
        self.assertEqual(len(r['branches']),6)
        minima=[b for b in r['branches'] if b['positive_physical_Hessian']]
        self.assertEqual(len(minima),2)
        self.assertEqual(sum(b['global_minimum'] for b in r['branches']),1)
        self.assertTrue(any(b['source_sign']==-1 and not b['global_minimum'] for b in minima))
        self.assertTrue(all(not b['positive_physical_Hessian'] for b in r['branches'] if b['Higgs_branch']=='Higgs_boundary'))

    def test_CP_tie_and_critical_flat_branch(self):
        r=biased_stationary_branches(self.model,self.bath,0)
        self.assertEqual(sum(b['global_minimum'] for b in r['branches']),2)
        # Portal-free unit CP transition occurs at exactly rational T=1.
        m=WallModel(1.,1.,1.,10.,0.);b=HiggsWall(portal=0.,v_GeV=.1)
        r=biased_stationary_branches(m,b,1)
        self.assertEqual(sum(z['global_minimum'] for z in r['branches']),1)
        self.assertTrue(any(z['global_minimum'] and z['reduced_source_curvature_sign']==0 for z in r['branches']))

    def test_bias_switch_and_input_guards(self):
        m=replace(self.model,bias_h0_GeV3=1e-13,bias_onset_GeV=3000.)
        self.assertEqual(Q(biased_stationary_branches(m,self.bath,3000)['exact_bias_over_v3']),0)
        with self.assertRaises(ValueError):unbiased_global_vacuum(m,self.bath,10)
        with self.assertRaises(ValueError):real_root_intervals((1,0,0,0,1))
        with self.assertRaises(ValueError):HiggsWall(portal=-1)


class CoupledWallStability(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.model=WallModel(30000.,.1,.025000033333333335,300000.,3000.)
        cls.bath=HiggsWall();cls.wall=solve_coupled_wall(cls.model,cls.bath)
        cls.coarse=fluctuation_spectrum(cls.wall,central_nodes=250)
        cls.fine=fluctuation_spectrum(cls.wall,central_nodes=500)

    def test_scalar_modes_by_independent_symbolic_differentiation(self):
        import sympy as s
        x=s.symbols('x',real=True);V=4-6/s.cosh(x)**2
        for psi,e in [(1/s.cosh(x)**2,0),(s.sinh(x)/s.cosh(x)**2,3)]:
            self.assertEqual(s.simplify(-s.diff(psi,x,2)+(V-e)*psi),0)
        self.assertAlmostEqual(scalar_reference(self.model)['shape_mass_GeV'],11618.95003862225)

    def test_hessian_by_independent_symbolic_potential(self):
        import sympy as s
        u,y,h=s.symbols('u y h');a=s.Rational(1,10);m=10;h0=s.Rational(246,30000);kap=s.Rational(1,10**7);lamH=s.Rational(13,100)
        V=s.Rational(1,40)*(u*u-1)**2+m*m*(y+a*u*u/m**2)**2/2+lamH*(h*h-h0*h0+kap/lamH*(u*u-1))**2/4
        point={u:s.Rational(2,5),y:s.Rational(-1,10000),h:s.Rational(1,100)}
        exact=np.array(s.hessian(V,(u,y,h)).subs(point)).astype(float)
        actual=potential_and_hessian(self.model,self.bath,.4,-.0001,.01)[1]
        np.testing.assert_allclose(actual,exact,rtol=2e-14,atol=1e-16)

    def test_three_field_wall_bounds_first_integral_and_Higgs_tail(self):
        r=self.wall['report'];bounds=Higgs_bath_completion(self.model)['three_field_tension_bounds_GeV3']
        self.assertTrue(bounds[0]<=r['tension_GeV3']<=bounds[1])
        self.assertLess(r['first_integral_maximum_error'],1e-10)
        self.assertLess(r['maximum_BVP_relative_residual'],3e-10)
        self.assertGreater(r['central_Higgs_GeV'],246.)
        self.assertLess(r['central_Higgs_GeV'],246.1)
        self.assertAlmostEqual(r['profile']['radial_Higgs_GeV'][-1],246.,places=10)

    def test_refinement_translation_overlap_and_complete_discrete_positivity(self):
        a=self.coarse['translation']['eigenvalues_over_v2'][0];b=self.fine['translation']['eigenvalues_over_v2'][0]
        self.assertGreater(a/b,14);self.assertLess(a/b,18)
        self.assertGreater(self.fine['translation']['translation_overlaps'][0],.99999999)
        for r in [self.coarse,self.fine]:
            self.assertEqual(r['resolved_negative_modes'],0)
            self.assertTrue(all(r[p]['finite_matrix_Cholesky_positive'] for p in ('translation','opposite')))
            self.assertTrue(all(max(r[p]['normalized_backward_eigen_residuals'])<1e-12 for p in ('translation','opposite')))

    def test_bulk_threshold_and_embedded_source_shape_mode(self):
        masses=self.fine['vacuum_particle_masses_GeV'];self.assertAlmostEqual(masses[0],125.43588003433428,places=7)
        self.assertLess(masses[0],scalar_reference(self.model)['shape_mass_GeV'])
        threshold=self.fine['vacuum_thresholds_over_v2'][0]
        self.assertGreater(self.fine['opposite']['eigenvalues_over_v2'][0],threshold)

    def test_free_Higgs_box_levels_independent_of_wall_solver(self):
        m=replace(self.model,current_g_GeV=0.);b=HiggsWall(portal=0.)
        wall=solve_coupled_wall(m,b);r=fluctuation_spectrum(wall,central_nodes=150,tail_nodes=100)
        mh2=2*b.lam*(b.v_GeV/m.v_GeV)**2;L=wall['L']
        self.assertAlmostEqual(r['opposite']['eigenvalues_over_v2'][0]/(mh2+(pi/(2*L))**2),1.,places=6)
        self.assertAlmostEqual(r['translation']['eigenvalues_over_v2'][1]/(mh2+(pi/L)**2),1.,places=6)

    def test_biased_static_wall_rejected(self):
        with self.assertRaises(ValueError):solve_coupled_wall(replace(self.model,bias_h0_GeV3=1e-13,bias_onset_GeV=3000))

    def test_published_linear_Higgs_response_and_stationary_census(self):
        import json
        from develop_wall_stability import ROOT
        r=json.loads((ROOT/'receipts/flavor_cosmology/wall_stability.json').read_text())
        shift=r['three_field_wall']['central_Higgs_GeV']-self.bath.v_GeV
        self.assertLess(abs(shift/r['linear_Higgs_center_shift_GeV']-1),1e-4)
        self.assertEqual(len(r['thermal_stationary_snapshots'][0]['branches']),6)
        self.assertFalse(r['conclusions']['certified_coupled_continuum_stability'])


if __name__=='__main__':unittest.main()
