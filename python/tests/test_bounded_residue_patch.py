import copy
import unittest
from perfectpower.bounded_residue_patch import patch_packet, verify_patch, native_patch, evaluate
from perfectpower.query_service import dispatch


class PatchTests(unittest.TestCase):
    def packet(self):
        return patch_packet([[1,0,1],[-1,2,0]],[[-10,10],[0,100]],5,[1,1])

    def test_complete_signed_box(self):
        p=self.packet()
        self.assertEqual(p['points'],[[-9,81],[-4,16],[1,1],[6,36]])
        self.assertTrue(verify_patch(p))
        self.assertLess(p['candidate_count'],p['coarse_count'])

    def test_omitted_point_rejected(self):
        p=self.packet();p['points'].pop();self.assertFalse(verify_patch(p))

    def test_omitted_lift_rejected(self):
        p=self.packet();p['lift_candidates'].pop();self.assertFalse(verify_patch(p))

    def test_changed_source_rejected(self):
        p=self.packet();p['terms'][0][0]+=1;self.assertFalse(verify_patch(p))

    def test_changed_inverse_rejected(self):
        p=self.packet();p['taylor']['vertical_inverse']+=1;self.assertFalse(verify_patch(p))

    def test_auxiliary_point_substitution_rejected(self):
        p=self.packet();p['auxiliary']['points'][0][0]+=5;self.assertFalse(verify_patch(p))

    def test_singular_chart_rejected(self):
        with self.assertRaises(ValueError):
            patch_packet([[1,0,2],[-1,4,0]],[[-8,8],[-70,70]],3,[0,0])

    def test_composite_rejected(self):
        with self.assertRaises(ValueError):
            patch_packet([[1,0,1],[-1,2,0]],[[0,10],[0,10]],9,[1,1])

    def test_budget_rejected_without_truncation(self):
        with self.assertRaises(ValueError):
            patch_packet([[1,0,1],[-1,2,0]],[[0,8192],[0,8192]],2,[0,0])

    def test_empty_packet_has_no_solution_theorem(self):
        p=patch_packet([[2,0,0],[-1,3,0],[1,0,2]],[[10,20],[-20,20]],7,[3,5])
        self.assertEqual(p['points'],[]);self.assertTrue(verify_patch(p))
        self.assertIn('theorem no_solution',native_patch(p))

    def test_mordell_curve_binding(self):
        p=patch_packet([[2,0,0],[-1,3,0],[1,0,2]],[[0,35],[-220,220]],7,[3,5])
        self.assertEqual(p['points'],[[3,5]])
        self.assertNotEqual(evaluate(p['terms'],129,1465),0)

    def test_query_round_trip(self):
        p=dispatch(None,{'op':'bounded_residue_patch','args':{'terms':[[1,0,1],[-1,2,0]],'bounds':[[-10,10],[0,100]],'prime':5,'residue':[1,1]}})
        self.assertTrue(dispatch(None,{'op':'verify_bounded_residue_patch','args':{'packet':p}})['valid'])
        self.assertFalse(p['global_height_bound'])
