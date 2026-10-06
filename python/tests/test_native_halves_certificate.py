from fractions import Fraction
import json
import tempfile
import unittest
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.native_halves_certificate import halves_certificate
from perfectpower.divisor_square import WorkLimit
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch

class NativeHalvesTests(unittest.TestCase):
    def test_anchor_and_four_element_coset(self):
        for spec,anchor,count in [([0,-2],[3,5],1),([-25,0],['25/4','75/8'],4),([1,'-1/4',1,'-1/2','-9/4'],[3,3],1)]:
            E=EllipticCurve(spec);target=E.mul(anchor,2)
            p=halves_certificate(spec,target,anchor=anchor)
            self.assertEqual(p['method'],'torsion_coset');self.assertEqual(len(p['completed_points']),count)
            self.assertEqual(p['completed_anchor'],encode_point(E.complete(anchor)))
            for v in p['completed_points']:self.assertEqual(E.mul(E.uncomplete(tuple(Fraction(x) for x in v)),2),target)
            self.assertIn('anchor_checked',p['lean']);self.assertFalse(p['execution_verified'])
    def test_empty_affine_and_branch_target(self):
        for spec,target in [([0,-2],[3,5]),([-1,0],[0,0])]:
            p=halves_certificate(spec,target)
            self.assertEqual(p['method'],'root_free_quartic');self.assertEqual(p['quartic_packet']['roots'],[])
            self.assertEqual(p['completed_points'],[]);self.assertIn('no_half_of_quartic_root_free',p['lean'])
            self.assertEqual(p['lean'].count('import '),3)
    def test_infinity(self):
        p=halves_certificate([-1,0],None)
        self.assertEqual(p['method'],'two_torsion');self.assertEqual(len(p['completed_points']),4)
    def test_discovered_anchor_and_invalid_input(self):
        E=EllipticCurve([0,-2]);target=E.mul([3,5],2)
        self.assertEqual(halves_certificate(E.specification,target)['method'],'torsion_coset')
        with self.assertRaises(ValueError):halves_certificate([0,-2],target,anchor=[3,-5])
        with self.assertRaises(ValueError):halves_certificate([0,-2],[0,0])
        with self.assertRaises(WorkLimit):halves_certificate([-25,0],None,divisor_work_limit=1)
    def test_public_service_and_registered_curve(self):
        with tempfile.TemporaryDirectory() as d,Catalogue(Path(d)/'db') as c:
            p=dispatch(c,dict(op='native_halves_certificate',args=dict(specification=[0,-2],target=[3,5])))
            self.assertEqual(p['method'],'root_free_quartic');json.dumps(p)
            c.register('elliptic_curve',dict(ainvs=[0,0,0,0,-2]),'E')
            p=dispatch(c,dict(op='call',object='E',method='native_halves',args=dict(target=[3,5])))
            self.assertEqual(p['completed_points'],[])
if __name__=='__main__':unittest.main()
