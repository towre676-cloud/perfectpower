import copy
import unittest
from perfectpower.residue_atlas import atlas_packet,verify_atlas,atlas_population,atlas_rank,atlas_select,atlas_scan,native_atlas,evaluate
from perfectpower.query_service import dispatch


class AtlasTests(unittest.TestCase):
    def cusp(self):return atlas_packet([[1,0,2],[-1,3,0]],2,3)

    def test_all_singular_children_retained(self):
        p=self.cusp();self.assertTrue(verify_atlas(p))
        self.assertEqual([len(r['roots']) for r in p['levels']],[2,6,12])
        singular=[n for n in p['levels'][1]['nodes'] if n['chart']=='singular']
        self.assertEqual(len(singular[0]['children']),4)

    def test_horizontal_chart(self):
        p=atlas_packet([[1,1,0],[-1,0,2]],2,4)
        self.assertEqual({n['chart'] for r in p['levels'] for n in r['nodes']},{'horizontal'})
        self.assertTrue(verify_atlas(p))

    def test_vertical_chart(self):
        p=atlas_packet([[1,0,1],[-1,2,0]],5,2)
        self.assertEqual({n['chart'] for r in p['levels'] for n in r['nodes']},{'vertical'})

    def test_singular_branch_death(self):
        p=atlas_packet([[1,0,2],[-1,2,0],[-2,0,0]],2,3)
        self.assertEqual([len(r['roots']) for r in p['levels']],[2,0,0])
        self.assertTrue(p['global_obstruction']);self.assertTrue(verify_atlas(p))
        self.assertIn('no_integer_solution',native_atlas(p,[[0,0],[0,0]]))

    def test_omitted_root_rejected(self):
        p=self.cusp();p['roots'].pop();self.assertFalse(verify_atlas(p))

    def test_omitted_intermediate_branch_rejected(self):
        p=self.cusp();p['levels'][1]['nodes'][0]['children'].pop();self.assertFalse(verify_atlas(p))

    def test_corrupt_chart_rejected(self):
        p=self.cusp();p['levels'][1]['nodes'][0]['chart']='vertical';self.assertFalse(verify_atlas(p))

    def test_corrupt_derivative_rejected(self):
        p=self.cusp();p['levels'][1]['nodes'][0]['dx']+=2;self.assertFalse(verify_atlas(p))

    def test_source_mutation_rejected(self):
        p=self.cusp();p['terms'][0][0]+=1;self.assertFalse(verify_atlas(p))

    def test_bool_coordinate_rejected(self):
        p=self.cusp();p['levels'][0]['roots'][0][0]=False;self.assertFalse(verify_atlas(p))

    def test_composite_rejected(self):
        with self.assertRaises(ValueError):atlas_packet([[1,0,1]],4,2)

    def test_modulus_budget_rejected(self):
        with self.assertRaises(ValueError):atlas_packet([[1,0,1]],5,4)

    def test_work_budget_rejected(self):
        with self.assertRaises(ValueError):atlas_packet([[1,0,1]],5,2,work_limit=26)

    def test_huge_population_exact(self):
        p=atlas_packet([[1,0,1],[-1,2,0]],5,2)
        self.assertEqual(atlas_population(p,[[-10**12,10**12],[-10**12,10**12]])['count'],160000000000480000000001)

    def test_signed_rectangle_count_and_addressing(self):
        p=self.cusp();bounds=[[-9,11],[-8,7]];m=p['modulus']
        expected=[]
        for a,b in p['roots']:
            expected.extend([[x,y] for x in range(-9,12) for y in range(-8,8) if x%m==a and y%m==b])
        self.assertEqual(atlas_population(p,bounds)['count'],len(expected))
        for i,z in enumerate(expected):
            self.assertEqual(atlas_select(p,bounds,i),z);self.assertEqual(atlas_rank(p,bounds,z),i)

    def test_large_rank_roundtrip(self):
        p=self.cusp();b=[[-10**12,10**12],[-10**12,10**12]];count=atlas_population(p,b)['count']
        for i in [0,1,count//2,count-1]:self.assertEqual(atlas_rank(p,b,atlas_select(p,b,i)),i)

    def test_select_outside(self):
        p=self.cusp();b=[[0,0],[0,0]]
        with self.assertRaises(IndexError):atlas_select(p,b,-1)
        with self.assertRaises(IndexError):atlas_select(p,b,1)

    def test_rank_nonmember(self):
        with self.assertRaises(ValueError):atlas_rank(self.cusp(),[[0,8],[0,8]],[1,0])

    def test_complete_scan_source(self):
        p=self.cusp();b=[[-10,10],[-10,10]]
        expected=[[x,y] for x in range(-10,11) for y in range(-10,11) if evaluate(p['terms'],x,y)==0]
        self.assertEqual(atlas_scan(p,b)['points'],expected)

    def test_scan_budget_no_partial_result(self):
        with self.assertRaises(ValueError):atlas_scan(self.cusp(),[[-10**12,10**12],[-10**12,10**12]])

    def test_empty_rectangle_population(self):
        p=self.cusp();b=[[1,1],[0,0]];self.assertEqual(atlas_population(p,b)['count'],0)
        self.assertEqual(atlas_scan(p,b)['points'],[])

    def test_native_budget_explicit(self):
        p=atlas_packet([[1,0,1]],2,6)
        with self.assertRaises(ValueError):native_atlas(p,[[0,0],[0,0]])

    def test_query_operations(self):
        p=dispatch(None,{'op':'residue_atlas','args':{'terms':[[1,0,1]],'prime':2,'exponent':2}})
        self.assertTrue(dispatch(None,{'op':'verify_residue_atlas','args':{'packet':p}})['valid'])
        b=[[-5,5],[-5,5]];z=dispatch(None,{'op':'residue_atlas_select','args':{'packet':p,'bounds':b,'index':0}})
        self.assertEqual(dispatch(None,{'op':'residue_atlas_rank','args':{'packet':p,'bounds':b,'point':z}}),0)
        self.assertIn('count_checked',dispatch(None,{'op':'native_residue_atlas','args':{'packet':p,'bounds':b}})['lean_source'])
