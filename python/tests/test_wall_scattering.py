from fractions import Fraction as Q
from math import pi,sqrt
import unittest
import numpy as np
from scipy.integrate import quad
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall,solve_coupled_wall,potential_and_hessian
from perfectpower.wall_scattering import outgoing_wavenumbers,weak_portal_shape_width,exact_shape_channel_conditions,outgoing_shape_pole,wall_scattering,reflection_amplitude,_potential


class ShapeRadiationAlgebra(unittest.TestCase):
    def test_form_factor_against_independent_real_space_integral(self):
        m=WallModel(1,.1,.025,10,0);b=HiggsWall(portal=1e-5,v_GeV=.1)
        r=weak_portal_shape_width(m,b);p=r['p']
        actual=2*quad(lambda x:np.tanh(x)**2/np.cosh(x)*np.cos(p*x),0,40,epsabs=1e-13)[0]
        self.assertAlmostEqual(actual,r['form_factor'],places=11)
        norm=quad(lambda x:1/np.cosh(x)**2*np.tanh(x)**2,-30,30)[0]
        self.assertAlmostEqual(norm,Q(2,3),places=12)

    def test_exact_channel_and_polynomial_node(self):
        m=WallModel(1,.1,.025,10,0)
        node=exact_shape_channel_conditions(m,HiggsWall(lam=.05,v_GeV=1))
        self.assertTrue(node['open']);self.assertTrue(node['leading_radiation_node'])
        self.assertEqual(Q(node['shape_energy_over_v2']),Q(3,20))
        self.assertEqual(weak_portal_shape_width(m,HiggsWall(portal=.01,lam=.05,v_GeV=1))['width_GeV'],0)
        closed=weak_portal_shape_width(m,HiggsWall(v_GeV=2))
        self.assertFalse(closed['open']);self.assertEqual(closed['width_GeV'],0)

    def test_width_is_quadratic_and_has_dimensionful_scaling(self):
        m=WallModel(1,.1,.025,10,0);a=weak_portal_shape_width(m,HiggsWall(portal=1e-4,v_GeV=.1))
        b=weak_portal_shape_width(m,HiggsWall(portal=2e-4,v_GeV=.1))
        self.assertAlmostEqual(b['width_GeV']/a['width_GeV'],4)
        c=weak_portal_shape_width(WallModel(10,.1,.025,100,0),HiggsWall(portal=1e-4,v_GeV=1))
        self.assertAlmostEqual(c['width_GeV']/a['width_GeV'],10)

    def test_outgoing_sheet_open_grows_closed_decays(self):
        q=outgoing_wavenumbers(.15-1e-6j,[.001,.2,100],[True,False,False])
        self.assertGreater(q[0].real,0);self.assertLess(q[0].imag,0)
        self.assertTrue(all(q[j].imag>0 for j in (1,2)))


class NumericalWallScattering(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.model=WallModel(30000,.1,.025,300000,3000)
        cls.wall=solve_coupled_wall(cls.model,HiggsWall(portal=.01,v_GeV=3000))
        cls.pole=outgoing_shape_pole(cls.wall,tol=1e-9)

    def test_vectorized_operator_matches_original_Hessian(self):
        x=np.array([0.,1.,10.,100.]);actual=_potential(self.wall,x)
        for i,z in enumerate(self.wall['solution'].sol(x).T):
            np.testing.assert_allclose(actual[i],potential_and_hessian(self.model,self.wall['bath'],*z[:3])[1],rtol=1e-14,atol=1e-16)

    def test_outgoing_pole_current_identity_and_controls(self):
        r=self.pole
        self.assertGreater(r['width_GeV'],1);self.assertLess(r['width_GeV'],1.5)
        self.assertLess(r['energy_over_v2'][1],0)
        self.assertLess(r['current_identity_relative_error'],2e-7)
        self.assertLess(r['boundary_residual'],1e-12)
        self.assertEqual(r['open_channels'],[True,False,False])
        shorter=outgoing_shape_pole(self.wall,radius=self.wall['L']*.75,tol=1e-9)
        self.assertLess(abs(shorter['width_GeV']/r['width_GeV']-1),1e-3)

    def test_real_axis_resonance_and_full_line_flux(self):
        E=self.pole['energy_over_v2'][0];gamma=-self.pole['energy_over_v2'][1]
        center=wall_scattering(self.wall,E,tol=1e-8)
        side=wall_scattering(self.wall,E+3*gamma,tol=1e-8)
        self.assertGreater(center['reflection_probability'],.99)
        self.assertLess(side['reflection_probability'],.12)
        for r in (center,side):
            self.assertLess(r['full_line_flux_error'],1e-9)
            for parity in ('even_Higgs','odd_Higgs'):self.assertLess(r[parity]['flux_error'],1e-9)

    def test_decoupled_free_channel_and_embedded_bound_state(self):
        m=WallModel(1,.1,.025,10,0);w=solve_coupled_wall(m,HiggsWall(portal=0,v_GeV=.1))
        p=outgoing_shape_pole(w,tol=1e-9)
        self.assertLess(abs(p['energy_over_v2'][0]-.15),1e-10)
        self.assertEqual(p['width_GeV'],0)
        r=wall_scattering(w,.12,tol=1e-8)
        self.assertLess(r['reflection_probability'],1e-14)
        self.assertAlmostEqual(r['transmission_probability'],1,places=9)
        self.assertAlmostEqual(r['even_Higgs']['amplitude'][0],1,places=6)
        self.assertAlmostEqual(r['odd_Higgs']['amplitude'][0],-1,places=6)

    def test_small_portal_agrees_with_independent_analytic_width(self):
        m=WallModel(1,.1,.025,10,0);b=HiggsWall(portal=1e-6,v_GeV=.1)
        w=solve_coupled_wall(m,b);p=outgoing_shape_pole(w,tol=1e-9)
        analytic=weak_portal_shape_width(m,b)['width_GeV']
        self.assertLess(abs(p['width_GeV']/analytic-1),1e-3)

    def test_polynomial_node_suppresses_but_does_not_eliminate_radiation(self):
        m=WallModel(1,.1,.025,10,0);width=[]
        for kap in [1e-4,2e-4]:
            w=solve_coupled_wall(m,HiggsWall(portal=kap,lam=.05,v_GeV=1))
            width.append(outgoing_shape_pole(w,tol=1e-9)['width_GeV'])
        self.assertGreater(width[0],0)
        self.assertGreater(width[1]/width[0],15);self.assertLess(width[1]/width[0],17)

    def test_rejects_wrong_channel_and_unphysical_radius(self):
        with self.assertRaises(ValueError):reflection_amplitude(self.wall,1000)
        with self.assertRaises(ValueError):reflection_amplitude(self.wall,.15,parity='bad')
        with self.assertRaises(ValueError):outgoing_shape_pole(self.wall,radius=2*self.wall['L'])


if __name__=='__main__':unittest.main()
