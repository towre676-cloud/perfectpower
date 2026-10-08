import unittest
from dataclasses import replace
try:
    import numpy as np
except ImportError:
    raise unittest.SkipTest("optional wall-formation tests require NumPy")
from perfectpower.wall_kibble_zurek import FormationInputs,lattice_modes,linear_bath_factors,nonlinear_flow,step,wall_length,temperature_bridge,simulate,coupled_timestep_check

class FormationDynamics(unittest.TestCase):
    def test_exact_quartic_flow_and_semigroup(self):
        u=np.linspace(-3,3,101)
        a=nonlinear_flow(nonlinear_flow(u,.07,2),.13,2)
        self.assertLess(np.max(abs(a-nonlinear_flow(u,.2,2))),1e-15)
        self.assertTrue(np.all(abs(a)<=abs(u)))

    def test_OU_factors_reproduce_stationary_covariance(self):
        k2=lattice_modes(32,16);m=.5;dt=.17;theta=.01;area=.25
        decay,sigma=linear_bath_factors(k2,m,dt,3,theta,area)
        var=theta/area/(k2+m)
        self.assertLess(np.max(abs(decay**2*var+sigma**2-var)),1e-16)

    def test_OU_zero_and_unstable_mode_limits(self):
        q=np.array([[0.,.5,1.]])
        d,s=linear_bath_factors(q,-.5,.1,2,.01,.25)
        self.assertTrue(np.all(s>0));self.assertGreater(d[0,0],1)
        self.assertAlmostEqual(s[0,1]**2,2*.01/.25*.1/2,places=15)

    def test_deterministic_time_refinement_is_second_order(self):
        p=FormationInputs(nodes=32,length=32,replicas=2,noise_temperature=0);k2=lattice_modes(32,32)
        x=np.arange(32);u=.3*np.cos(2*np.pi*x/32)[None,None,:]*np.ones((2,32,1))
        values=[]
        for dt in [.1,.05,.025,.0125]:
            z=u.copy();rng=np.random.default_rng(2)
            for _ in range(round(1/dt)):z=step(z,k2,-.3,dt,p,rng)
            values.append(z)
        a=np.linalg.norm(values[0]-values[3]);b=np.linalg.norm(values[1]-values[3])
        self.assertGreater(a/b,3.8);self.assertLess(a/b,4.4)

    def test_axis_and_diagonal_periodic_interface_lengths(self):
        n=128;L=32;x=np.arange(n)*L/n;y=x[:,None]
        u=np.broadcast_to(np.sin(2*np.pi*x/L+.17),(n,n))
        self.assertAlmostEqual(float(wall_length(u,L/n)),2*L,places=10)
        v=np.sin(2*np.pi*(x+y)/L+.17)
        self.assertAlmostEqual(float(wall_length(v,L/n)),2*np.sqrt(2)*L,places=9)

    def test_circle_interface_converges_to_geometric_length(self):
        values=[]
        for n in [64,128,256]:
            x=(np.arange(n)+.5)*32/n-16
            u=np.sqrt(x[:,None]**2+x[None,:]**2)-7
            values.append(abs(float(wall_length(u,32/n))-2*np.pi*7))
        self.assertLess(values[-1],.01);self.assertLess(values[-1],values[-2]*.4)

    def test_declared_thermal_bridge_preserves_restored_Higgs(self):
        p=FormationInputs();a=temperature_bridge(-.5,p);b=temperature_bridge(0,p)
        self.assertGreater(a['restored_Higgs_minimum_curvature_GeV2'],0)
        self.assertGreater(b['declared_temperature_GeV'],a['declared_temperature_GeV'])
        self.assertGreater(b['declared_temperature_GeV'],790);self.assertLess(b['declared_temperature_GeV'],800)

    def test_small_run_replays_and_has_finite_observables(self):
        p=FormationInputs(nodes=16,length=16,replicas=2,equilibration=1,dt=.1)
        a=simulate(4,inputs=p,sample_multiples=(0,2));b=simulate(4,inputs=p,sample_multiples=(0,2))
        self.assertEqual(a['final_field_sha256'],b['final_field_sha256'])
        self.assertTrue(np.all(np.isfinite(a['observations'][-1]['energy_density'])))

    def test_coupled_OU_composition_has_correct_coarse_covariance(self):
        k2=lattice_modes(32,32)
        for mass in [-.3,0,.5]:
            d,s=linear_bath_factors(k2,mass,.1,1,.001,1)
            df,sf=linear_bath_factors(k2,mass,.05,1,.001,1)
            self.assertLess(np.max(abs(d-df*df)),1e-15)
            self.assertLess(np.max(abs(s*s-((df*sf)**2+sf**2))),1e-16)

    def test_coupled_paths_replay_with_small_difference(self):
        p=FormationInputs(nodes=16,length=16,replicas=2,equilibration=1)
        a=coupled_timestep_check(4,inputs=p,time_over_hat=2)
        b=coupled_timestep_check(4,inputs=p,time_over_hat=2)
        self.assertEqual(a,b)
        self.assertLess(max(a['replica_field_RMS_difference']),.001)

    def test_invalid_inputs_rejected(self):
        for kwargs in [{'dt':0},{'nodes':15},{'noise_temperature':-1}]:
            with self.assertRaises(ValueError):FormationInputs(**kwargs)
        with self.assertRaises(ValueError):simulate(-1)

if __name__=='__main__':unittest.main()
