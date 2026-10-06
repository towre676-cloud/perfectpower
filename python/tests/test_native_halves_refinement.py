import hashlib,json,tempfile,unittest
from pathlib import Path
from fractions import Fraction as Q
from perfectpower.native_halves_certificate import halves_certificate
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.query_service import dispatch
from perfectpower.catalogue import Catalogue
from perfectpower.divisor_square import WorkLimit

class RefinementTests(unittest.TestCase):
    def test_original_generalized_coordinates_and_exact_list(self):
        E=EllipticCurve([1,'-1/4',1,'-1/2','-9/4']);target=E.mul([3,3],2)
        p=halves_certificate(E.specification,target,anchor=[3,3])
        self.assertEqual(p['original_points'],[['3','3']]);self.assertEqual(p['completed_points'],[['3','5']])
        self.assertEqual(p['schema'],'pp-native-halves-certificate/2')
        for name in ['original_halves_complete','original_json_list_checked','original_target_checked','literal_fibre_complete']:
            self.assertIn(name,p['lean'])
        self.assertEqual(p['source_sha256'],hashlib.sha256(p['lean'].encode()).hexdigest())
    def test_nonsquare_quartic_lifts_close_empty_fibre(self):
        p=halves_certificate([1,0],[0,0]);self.assertEqual(p['method'],'signed_quartic_lifts')
        self.assertEqual(p['quartic_packet']['roots'],['-1','1']);self.assertEqual(p['original_points'],[])
        self.assertIn('EllipticQuarticLifts.fibre_complete',p['lean'])
    def test_both_signs_are_checked_by_actual_doubling(self):
        E=EllipticCurve([0,-7])
        for anchor in [[2,1],[2,-1]]:
            p=halves_certificate(E.specification,E.mul(anchor,2),route='quartic')
            self.assertEqual(p['original_points'],[encode_point(E.checked(anchor))]);self.assertEqual(p['method'],'signed_quartic_lifts')
            self.assertEqual(p['quartic_packet']['roots'],['2'])
    def test_coset_order_matches_literal_native_list(self):
        E=EllipticCurve([-25,0]);anchor=['25/4','75/8'];target=E.mul(anchor,2)
        p=halves_certificate(E.specification,target,anchor=anchor)
        expected=[encode_point(E.add(anchor,t)) for t in [None,*E.two_torsion()]]
        self.assertEqual(p['original_points'],expected)
        for pt in p['original_points']:self.assertEqual(E.mul(pt,2),target)
    def test_service_and_registered_route(self):
        with tempfile.TemporaryDirectory() as d,Catalogue(Path(d)/'db') as c:
            c.register('elliptic_curve',dict(ainvs=[0,-7]),'E')
            target=EllipticCurve([0,-7]).mul([2,1],2)
            p=dispatch(c,dict(op='call',object='E',method='native_halves',args=dict(target=encode_point(target),route='quartic')))
            self.assertEqual(p['original_points'],[['2','1']]);json.dumps(p)
    def test_budgets_and_route_validation(self):
        with self.assertRaises(ValueError):halves_certificate([0,-7],[2,1],route='other')
        with self.assertRaises(WorkLimit):halves_certificate([0,-7],EllipticCurve([0,-7]).mul([2,1],2),route='quartic',divisor_work_limit=1)
if __name__=='__main__':unittest.main()
