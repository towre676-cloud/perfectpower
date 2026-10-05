import unittest
from fractions import Fraction
import json
from pathlib import Path
try:
    import numpy as np
except ImportError:
    np=None
from perfectpower.flavor_prediction import exponent_domain,phase_domain,golden_depth_polynomial

class Algebra(unittest.TestCase):
    def test_domain_count_and_exact_duplicates(self):
        a=exponent_domain(); self.assertEqual(len(a),61651);self.assertEqual(len(set(a)),len(a))
        self.assertTrue(all(isinstance(v,Fraction) for r in a for v in r))
        self.assertEqual(len(phase_domain()),47)
    def test_golden_polynomial_independent_expansion(self):
        u,v,w=map(Fraction,['.22431','.0411','.00352'])
        # Expanded independently: w^6-2w^4+w^2+3uv w^3-3uv w+u^2v^2.
        self.assertEqual(golden_depth_polynomial(u,v,w),w**6-2*w**4+w*w+3*u*v*w**3-3*u*v*w+u*u*v*v)
    def test_exact_cyclotomic_carrier(self):
        from perfectpower.flavor_prediction import cyclotomic_golden_carrier
        r=cyclotomic_golden_carrier()
        self.assertEqual(r['coefficient_identity_remainder'],['0'])
        self.assertEqual(r['root_unity_identity_remainder'],['0'])
        self.assertEqual(r['norm'],'1');self.assertEqual(r['trace'],'24')
        self.assertTrue(all(v!=['0'] for v in r['proper_power_nonzero_remainders'].values()))
    def test_guards(self):
        for s in [True,-1,6]:
            with self.assertRaises(ValueError):exponent_domain(support=s)
        with self.assertRaises(ValueError):phase_domain([0])
        with self.assertRaises(ValueError):golden_depth_polynomial(.2,'1/2','1/3')

@unittest.skipIf(np is None,'optional numpy unavailable')
class Physics(unittest.TestCase):
    def test_unitarity_and_anchors(self):
        from perfectpower.flavor_prediction import ckm_from_depth
        c=np.linspace(0,2,101);d=np.linspace(.01,np.pi-.01,101)
        V=ckm_from_depth(c,d,.22431,.0411)
        self.assertLess(np.max(np.abs(V@V.conj().swapaxes(-1,-2)-np.eye(3))),8e-16)
        self.assertLess(np.max(np.abs(np.abs(V[:,0,1])-.22431)),1e-16)
        self.assertLess(np.max(np.abs(np.abs(V[:,1,2])-.0411)),1e-16)
        w=np.abs(V[:,0,2]);self.assertLess(np.max(np.abs(w-w**3-c*.22431*.0411)),1e-17)
    def test_invariants_independently(self):
        from perfectpower.flavor_prediction import ckm_from_depth,observables
        c=.38196601125010515;d=11*np.pi/30;V=ckm_from_depth(c,d,.22431,.0411);o=observables(V)
        t=abs(V[0,2]);c13=(1-t*t)**.5;s12=.22431/c13;s23=.0411/c13
        direct=(1-s12*s12)**.5*(1-s23*s23)**.5*c13*c13*s12*s23*t*np.sin(d)
        self.assertAlmostEqual(o['J'],direct,places=17)
        # The three internal triangle angles sum to pi.
        alpha=np.angle(-V[2,0]*V[2,2].conj()/(V[0,0]*V[0,2].conj()))
        beta=np.angle(-V[1,0]*V[1,2].conj()/(V[2,0]*V[2,2].conj()))
        self.assertAlmostEqual(alpha+beta+o['gamma']*np.pi/180,np.pi,places=14)
    def test_training_schema_excludes_holdouts(self):
        from perfectpower.flavor_prediction import fit
        root=Path(__file__).resolve().parents[2];t=json.loads((root/'receipts/flavor_prediction/training.json').read_text())
        r=fit(t,model='legacy',quadrature_order=1,samples_per_node=128)
        self.assertIn('Vub',r['predictions'])
        for key in ['Vub','sin2beta','heldout']:
            wrong=dict(t);wrong[key]=0
            with self.assertRaises(ValueError):fit(wrong,model='legacy',quadrature_order=1,samples_per_node=128)
    def test_weighted_quantiles(self):
        from perfectpower.flavor_prediction import weighted_summary
        q=weighted_summary([1,2,3],[1,8,1]);self.assertEqual(q['median'],2);self.assertEqual(q['mean'],2)
