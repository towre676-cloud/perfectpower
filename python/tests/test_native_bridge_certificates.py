from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import random
import tempfile
import unittest
from perfectpower.native_rational_certificate import rational_certificate, two_torsion_certificate
from perfectpower.native_residue_certificate import residue_certificate
from perfectpower.native_braid_certificate import braid_certificate
from perfectpower.elliptic_arithmetic import rational_root_certificate
from perfectpower.divisor_square import WorkLimit
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch


def bounded(lo,hi,*extra):
    return dict(op='and',args=[dict(poly=[-lo,1],relation='>='),dict(poly=[-hi,1],relation='<=')]+list(extra))


class NativeBridgeCertificateTests(unittest.TestCase):
    def test_rational_original_source_nonmonic_repeated_zero_and_constant(self):
        for f,expected in [(['-3/2',0,6],['-1/2','1/2']),([0,0,-1,0,1],['-1','0','1']),
                           ([2],[]),([1,0,1],[]),([-1,3,-3,1],['1']),([-2,-4],['-1/2'])]:
            result=rational_certificate(f)
            self.assertEqual(result['roots'],expected)
            self.assertIn('complete_nonmonic',result['lean'])
            self.assertIn('decide +kernel',result['lean'])
            self.assertFalse(result['execution_verified'])
        self.assertNotEqual(rational_certificate([-1,0,1])['namespace'],rational_certificate([-2,0,2])['namespace'])

    def test_root_packet_mutation_rejected_and_work_budget_enforced(self):
        receipt=rational_root_certificate([Q(-1,4),0,1])
        bad=deepcopy(receipt);bad['roots']=['0']
        with self.assertRaises(ValueError):rational_certificate([-1,0,4],receipt=bad)
        bad=deepcopy(receipt);bad['integer_certificate']['nodes'][0][2]+=1
        with self.assertRaises(ValueError):rational_certificate([-1,0,4],receipt=bad)
        for coeff in ([0],[False,1],['1.5',1]):
            with self.assertRaises(ValueError):rational_certificate(coeff)
        with self.assertRaises(WorkLimit):rational_certificate([-(10**20),1])
        with self.assertRaises(ValueError):rational_certificate([1,1],node_limit=True)

    def test_huge_noncoprime_residue_source_no_enumeration(self):
        predicate=bounded(-10**30,10**30,dict(poly=[0,1],relation='=',modulus=6,value=1),
                          dict(poly=[0,1],relation='=',modulus=9,value=4))
        result=residue_certificate(predicate)
        self.assertEqual(result['cardinality'],111111111111111111111111111111)
        self.assertEqual(result['cells'][0]['modulus'],18)
        self.assertEqual(result['cells'][0]['residue'],13)
        self.assertIn('population_count',result['lean'])
        self.assertLess(len(result['lean']),5000)

    def test_residue_boolean_affine_sources_match_brute_force(self):
        rng=random.Random(10489)
        for _ in range(50):
            lo=rng.randrange(-30,0);hi=rng.randrange(1,30);m=rng.randrange(1,9)
            a=rng.randrange(-3,4);b=rng.randrange(-7,8);v=rng.randrange(-1,m+1)
            atom=dict(poly=[b,a],relation='<',modulus=m,value=v)
            pred=bounded(lo,hi,dict(op='not',args=[atom]))
            result=residue_certificate(pred)
            expected=[x for x in range(lo,hi+1) if not (a*x+b)%m<v]
            self.assertEqual(result['cardinality'],len(expected))
            actual=[x for x in range(lo,hi+1) if any(c['lower']<=x<=c['upper'] and x%c['modulus']==c['residue'] for c in result['cells'])]
            self.assertEqual(actual,expected)
        self.assertEqual(residue_certificate(False)['cardinality'],0)
        self.assertEqual(residue_certificate(bounded(5,-5))['cardinality'],0)
        with self.assertRaises(ValueError):residue_certificate(True)
        with self.assertRaises(ValueError):residue_certificate(bounded(-3,3,dict(poly=[0,0,1],relation='>=')))
        with self.assertRaises(WorkLimit):residue_certificate(bounded(-100,100,dict(poly=[0,1],relation='!=',modulus=17,value=0)),cell_limit=2)

    def test_marked_braid_relations_and_inverse_words(self):
        for g in range(1,5):
            braid=braid_certificate(g,[1,2,1]);other=braid_certificate(g,[2,1,2])
            self.assertEqual(braid['receipt']['matrix'],other['receipt']['matrix'])
            inverse=braid_certificate(g,[1,2,3,-3,-2,-1])
            self.assertEqual(inverse['receipt']['matrix'],[[int(i==j) for j in range(2*g)] for i in range(2*g)])
            self.assertIn('wordMatrix',braid['lean'])
            self.assertIn('integral_symplectic',braid['lean'])
        with self.assertRaises(WorkLimit):braid_certificate(4,[1]*40)
        with self.assertRaises(WorkLimit):braid_certificate(1,[1]*65)
        with self.assertRaises(ValueError):braid_certificate(2,[False])

    def test_actual_two_torsion_bridge_and_registered_consumer(self):
        from perfectpower.elliptic_arithmetic import EllipticCurve
        result=EllipticCurve([-1,0]).native_two_torsion()
        self.assertEqual(result['two_torsion_cardinality'],4)
        self.assertIn('actual_two_torsion_complete',result['lean'])
        self.assertIn('smooth_checked',result['lean'])
        generalized=two_torsion_certificate(dict(ainvs=[1,2,3,-4,5]))
        self.assertEqual(generalized['completed_coefficients'],['9/4','-5/2','29/4'])
        with self.assertRaises(ValueError):two_torsion_certificate(dict(ainvs=[0,0]))
        with tempfile.TemporaryDirectory() as folder,Catalogue(Path(folder)/'db') as catalogue:
            catalogue.register('elliptic_curve',dict(ainvs=[-1,0]),'E')
            fresh=dispatch(catalogue,dict(op='call',object='E',method='native_two_torsion'))
        self.assertEqual(fresh['two_torsion_cardinality'],4)

    def test_cold_service_all_three_bridges(self):
        requests=[dict(op='native_rational_certificate',args=dict(coefficients=[-1,0,4])),
                  dict(op='native_residue_certificate',args=dict(predicate=bounded(-10,10,dict(poly=[0,1],relation='=',modulus=3,value=1)))),
                  dict(op='native_braid_certificate',args=dict(genus=2,word=[1,2,-1,3]))]
        with tempfile.TemporaryDirectory() as folder,Catalogue(Path(folder)/'db') as catalogue:
            results=[dispatch(catalogue,r) for r in requests]
        self.assertEqual(results[0]['roots'],['-1/2','1/2'])
        self.assertEqual(results[1]['cardinality'],7)
        self.assertEqual(results[2]['receipt']['genus'],2)


if __name__=='__main__':unittest.main()
