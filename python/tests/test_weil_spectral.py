import unittest
from fractions import Fraction as Q
from math import lcm
import sympy as S
from perfectpower import weil_spectral as W
from perfectpower import weil_commutant as C
from perfectpower.weil_orbit import closed_form
from perfectpower.divisor_square import WorkLimit
from perfectpower.query_service import dispatch

class WeilSpectralTests(unittest.TestCase):
    def test_original_coordinate_projectors(self):
        for n in (3,4,8,9,12,16,24,32,48,64):
            basis,table,weights,projects,rows,chars=W._spectral(n)
            self.assertEqual(len(projects),closed_form(n))
            self.assertEqual(sum(r['rank'] for r in rows),n)
            self.assertTrue(all(type(v) is Q for row in chars for v in row))
            for E in projects:
                den=lcm(*(x.denominator for row in E for x in row))
                self.assertTrue(C._check_basis(n,[tuple(tuple(int(x*den) for x in row) for row in E)]),n)
    def test_operator_spectrum_and_inverse_against_dense_matrix(self):
        for n in (3,4,8,9,12):
            basis,table,weights,projects,rows,chars=W._spectral(n)
            c=[str(x) for x in weights];p=W.operator_packet(n,c)
            A=S.Matrix(W._linear(basis,weights))
            self.assertEqual(Q(p['trace']),Q(A.trace()))
            self.assertEqual(Q(p['determinant']),Q(A.det()))
            inverse=S.Matrix(W._linear(basis,list(map(Q,p['inverse_coordinates']))))
            self.assertEqual(A*inverse,S.eye(n))
            self.assertEqual(sorted((Q(x),int(m)) for x,m in A.eigenvals().items()),
                             sorted((Q(x),m) for x,m in zip(p['eigenvalues'],p['multiplicities'])))
    def test_zero_operator(self):
        p=W.operator_packet(8,[0]*5)
        self.assertIsNone(p['inverse_coordinates']);self.assertEqual(p['determinant'],'0');self.assertEqual(p['trace'],'0')
    def test_compressed_all_level_ranks(self):
        for n in list(range(1,500))+[729,1024,3125,1000000]:
            p=W.decomposition_plan(n)
            self.assertEqual(p['dimension'],closed_form(n));self.assertEqual(sum(b['rank'] for b in p['blocks']),n)
            self.assertTrue(all(b['rank']>0 for b in p['blocks']))
        self.assertEqual(W.decomposition_plan(1000000)['dimension'],77)
    def test_clock_shift_level_four_exception(self):
        self.assertEqual([b['rank'] for b in W.decomposition_plan(4)['blocks']],[1,1,2])
        self.assertEqual(sorted(b['rank'] for b in W.decomposition_plan(64)['blocks']),[1,1,2,2,2,4,4,8,8,16,16])
    def test_cache_isolation(self):
        p=W.spectral_packet(9);p['blocks'][0]['coordinates'][0]='123';p['blocks'][0]['node'][0]='bad'
        q=W.spectral_packet(9);self.assertNotEqual(q['blocks'][0]['coordinates'][0],'123');self.assertNotEqual(q['blocks'][0]['node'][0],'bad')
    def test_inputs_and_budgets(self):
        for n in (0,-1,True,3.0,'3'):
            with self.assertRaises(ValueError):W.decomposition_plan(n)
            with self.assertRaises(ValueError):closed_form(n)
        with self.assertRaises(WorkLimit):W.decomposition_plan(1000001)
        with self.assertRaises(WorkLimit):W.spectral_packet(64,work_limit=1)
        with self.assertRaises(ValueError):W.operator_packet(3,[True,0])
        with self.assertRaises(ValueError):W.operator_packet(3,[1])
        with self.assertRaises(ValueError):W.operator_packet(3,['1e1000000000',0])
        with self.assertRaises(WorkLimit):W.operator_packet(3,['1'*1301,0])
        with self.assertRaises(ValueError):W.spectral_packet(3,include_matrices=1)
        with self.assertRaises(WorkLimit):W.operator_packet(64,[2**2047]+[0]*10)
    def test_json_service(self):
        p=dispatch(None,{'op':'weil_projector_plan','args':{'level':243}})
        self.assertEqual(p['dimension'],6)
        p=dispatch(None,{'op':'weil_spectral','args':{'level':4}})
        self.assertEqual(p['dimension'],3)
        p=dispatch(None,{'op':'weil_operator_spectrum','args':{'level':4,'coefficients':[1,0,0]}})
        self.assertEqual(p['determinant'],'1')

if __name__=='__main__':unittest.main()
