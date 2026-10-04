import unittest
from importlib.util import find_spec
from perfectpower.symplectic_surface import symplectic_reduce,pairing,surface_basis
from perfectpower.integer_lifting import verify_smith

class SymplecticTests(unittest.TestCase):
    def test_integral_reduction(self):
        for a in [[[0,1],[-1,0]],[[0,2,1,0],[-2,0,0,1],[-1,0,0,0],[0,-1,0,0]]]:
            r=symplectic_reduce(a)
            self.assertEqual(pairing(a,r['basis_columns']),r['standard_intersection'])
            self.assertTrue(all(verify_smith(c) for c in r['smith_transcripts']))
    @unittest.skipUnless(find_spec('numpy'), 'optional NumPy not installed')
    def test_period_normalization_contract(self):
        from perfectpower.symplectic_surface import normalize_periods
        r=symplectic_reduce([[0,1],[-1,0]])
        r.update(genus=1,intersection_matrix=[[0,1],[-1,0]])
        p=normalize_periods([[2,2j]],r)
        self.assertEqual(p['tau'],[[[0.0,1.0]]])
        self.assertTrue(p['positive_imaginary_part'])
        self.assertFalse(p['analytic_integrals_certified'])
    def test_nonsaturated_rejected(self):
        with self.assertRaises(ValueError):symplectic_reduce([[0,2],[-2,0]])
    @unittest.skipUnless(find_spec('numpy') and find_spec('scipy'), 'optional numerical dependencies not installed')
    def test_actual_surfaces(self):
        from perfectpower.conformal_mesh import hyperelliptic_mesh
        for coeff,g in [([-1,0,0,0,1],1),([0,-1,0,0,0,1],2),([-1,0,0,0,0,0,0,1],3)]:
            mesh=hyperelliptic_mesh(coeff,6);r=surface_basis(mesh)
            self.assertEqual(r['genus'],g);self.assertEqual(len(r['polygon_word']),4*g)
            self.assertEqual(len(r['dual_generator_cycles']),2*g)
            for cycle in r['dual_generator_cycles']:
                self.assertEqual(cycle[0][0],0);self.assertEqual(cycle[-1][1],0)
                self.assertTrue(all(x[1]==y[0] for x,y in zip(cycle,cycle[1:])))
