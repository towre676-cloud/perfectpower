import unittest
import numpy as np
from math import pi,sqrt
from perfectpower.wall_pair_decay import parity_continuum,pair_phase_space,continuum_pair_width
from perfectpower.wall_thermal_vectors import planar_boson_free_energy,thermal_relative_determinant

class ContinuumDecay(unittest.TestCase):
    def test_free_flux_normalization_both_parities(self):
        x=np.linspace(0,14,701);q=np.array([.001,.07,.4,1.8])
        r=parity_continuum(x,np.zeros_like(x),q)
        self.assertLess(np.max(abs(r['waves'][0]-np.cos(q[:,None]*x)/sqrt(pi))),2e-9)
        self.assertLess(np.max(abs(r['waves'][1]-np.sin(q[:,None]*x)/sqrt(pi))),2e-9)

    def test_positive_barrier_regular_solution(self):
        # Smooth Pöschl-Teller barrier: parity flux amplitudes at two radii.
        q=np.array([.04,.2,1.]);a=[]
        for R in [12,18]:
            x=np.linspace(0,R,1001);r=parity_continuum(x,.3/np.cosh(x)**2,q)
            a.append(r['waves'][:,:,0])
        self.assertLess(np.max(abs(a[0]-a[1])),2e-9)

    def test_massless_phase_space_triangle_area(self):
        k,l,w=pair_phase_space(7,0,36)
        self.assertAlmostEqual(w.sum(),49/2,places=12)
        self.assertTrue(np.all(k+l<7))

    def test_constant_overlap_exact_width_and_symmetry_factor(self):
        nodes=np.linspace(1e-12,9,21);G=np.zeros((2,21,21));G[0]=2
        a=continuum_pair_width(7,0,nodes,G,identical=True,species=3)
        b=continuum_pair_width(7,0,nodes,G,identical=False,species=3)
        self.assertAlmostEqual(a['width_GeV'],3*4/32,places=12)
        self.assertAlmostEqual(b['width_GeV'],2*a['width_GeV'],places=12)

    def test_threshold_and_positive_mass_domain(self):
        k,l,w=pair_phase_space(10,3,100)
        self.assertTrue(np.all(np.sqrt(k*k+9)+np.sqrt(l*l+9)<10))
        self.assertGreater(w.sum(),0)
        self.assertFalse(continuum_pair_width(6,3,[],[],order=8)['open'])

    def test_free_form_factor_matches_fourier_transform(self):
        from scipy.integrate import simpson
        x=np.linspace(0,12,3001);k=.7;l=.2;c=np.exp(-x*x)
        ee=2*simpson(c*np.cos(k*x)*np.cos(l*x)/pi,x=x)
        oo=2*simpson(c*np.sin(k*x)*np.sin(l*x)/pi,x=x)
        self.assertAlmostEqual(ee,(np.exp(-(k-l)**2/4)+np.exp(-(k+l)**2/4))/(2*sqrt(pi)),places=12)
        self.assertAlmostEqual(oo,(np.exp(-(k-l)**2/4)-np.exp(-(k+l)**2/4))/(2*sqrt(pi)),places=12)

    def test_invalid_momenta_rejected(self):
        with self.assertRaises(ValueError):parity_continuum(np.linspace(0,1,10),np.zeros(10),[0])
        with self.assertRaises(ValueError):pair_phase_space(-1,0)

class ThermalDeterminant(unittest.TestCase):
    def test_massless_planar_pressure(self):
        from scipy.special import zeta
        self.assertAlmostEqual(planar_boson_free_energy(0,2,terms=5000)/(-8*zeta(3)/(2*pi)),1,places=7)

    def test_free_box_cancellation(self):
        z=np.linspace(-1,1,401);r=thermal_relative_determinant(z,np.full_like(z,9),3,5)
        self.assertLess(abs(r['relative_thermal_free_energy_per_area_GeV3']),1e-8)

    def test_positive_barrier_monotonicity_and_mesh_convergence(self):
        a=[]
        for n in [201,401,801]:
            z=np.linspace(-2,2,n);V=9+2/np.cosh(3*z)**2
            a.append(thermal_relative_determinant(z,V,3,5)['relative_thermal_free_energy_per_area_GeV3'])
        self.assertTrue(all(v>0 for v in a))
        self.assertLess(abs(a[-1]-a[-2]),abs(a[-2]-a[-3])*.3)

    def test_negative_mode_rejected(self):
        z=np.linspace(-2,2,101)
        with self.assertRaises(ValueError):thermal_relative_determinant(z,np.full_like(z,-10),1,2)


class ThermalDamping(unittest.TestCase):
    def test_bose_inverse_decay_subtraction_enhances_retarded_rate(self):
        nodes=np.linspace(1e-12,9,31);G=np.ones((2,31,31))
        zero=continuum_pair_width(7,0,nodes,G,temperature=0)
        warm=continuum_pair_width(7,0,nodes,G,temperature=2)
        self.assertGreater(warm['width_GeV'],zero['width_GeV'])
        with self.assertRaises(ValueError):continuum_pair_width(7,0,nodes,G,temperature=-1)

    def test_physical_rescaling_of_mass_momenta_vertex_and_bath(self):
        nodes=np.linspace(1e-12,9,31);G=np.ones((2,31,31));a=4
        base=continuum_pair_width(7,1,nodes,G,temperature=2)
        scaled=continuum_pair_width(7*a,a,nodes*a,G*sqrt(a),temperature=2*a)
        self.assertAlmostEqual(scaled['width_GeV']/base['width_GeV'],a,places=12)

    def test_near_threshold_normal_momentum_suppression(self):
        # A barrier gives f_k~k in the core, so the pair kernel is ~k*l.
        nodes=np.linspace(1e-12,3,100);G=np.zeros((2,100,100));G[0]=nodes[:,None]*nodes
        rates=[continuum_pair_width(2+e,1,nodes,G,order=128)['width_GeV'] for e in [.002,.001]]
        self.assertAlmostEqual(rates[0]/rates[1],8,delta=.015)

if __name__=='__main__':unittest.main()
