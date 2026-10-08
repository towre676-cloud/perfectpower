import copy
import unittest
from perfectpower.residue_atlas import atlas_packet
from perfectpower.residue_atlas_product import product_packet
from perfectpower.residue_atlas_intersection_factored import (intersect_atlases, verify_intersection,
    intersection_contains, intersection_population, intersection_select, intersection_rank,
    intersection_scan, native_intersection)
from perfectpower.query_service import dispatch

PARABOLA = [[1,0,1],[-1,2,0]]
LINE = [[1,0,1],[-1,1,0]]
Y = [[1,0,1]]
Y_MINUS_ONE = [[1,0,1],[-1,0,0]]

class IntersectionTests(unittest.TestCase):
    def packet(self, limit=4096):
        return intersect_atlases([atlas_packet(PARABOLA,2,3),atlas_packet(LINE,2,2)],explicit_limit=limit)

    def test_different_sources_nested(self):
        p=self.packet()
        self.assertTrue(verify_intersection(p));self.assertEqual(p['modulus'],8)
        self.assertEqual(p['roots'],[[0,0],[1,1],[4,0],[5,1]])
        self.assertTrue(intersection_contains(p,[-3,9]))
        self.assertFalse(intersection_contains(p,[2,4]))

    def test_overlapping_products_lcm(self):
        p=intersect_atlases([product_packet(PARABOLA,[[2,2],[3,1]]),
                            product_packet(LINE,[[2,1],[3,2]])])
        self.assertTrue(verify_intersection(p));self.assertEqual(p['modulus'],36)
        expected=[[x,y] for x in range(36) for y in range(36) if (y-x*x)%12==0 and (y-x)%18==0]
        self.assertEqual(p['roots'],expected)

    def test_idempotence_permutation_and_redundancy(self):
        a=atlas_packet(PARABOLA,2,3);b=atlas_packet(LINE,2,2)
        self.assertEqual(intersect_atlases([a,b]),intersect_atlases([b,a,a]))
        p=intersect_atlases([a,atlas_packet(PARABOLA,2,1)])
        self.assertEqual(p['roots'],a['roots'])
        p['constraints'][0]['terms'][0][0]=100
        self.assertNotEqual(p['constraints'][0]['terms'],a['terms'])
        self.assertTrue(verify_intersection(intersect_atlases([a])))

    def test_empty_global_obstruction(self):
        p=intersect_atlases([atlas_packet(Y,2,2),atlas_packet(Y_MINUS_ONE,2,1)],explicit_limit=1)
        self.assertTrue(verify_intersection(p));self.assertTrue(p['global_obstruction'])
        self.assertEqual(p['roots'],[]);self.assertEqual(intersection_population(p,[[-10,10],[-10,10]])['count'],0)
        self.assertEqual(intersection_scan(p,[[-10,10],[-10,10]])['points'],[])
        with self.assertRaises(IndexError):intersection_select(p,[[0,1],[0,1]],1)

    def test_factored_signed_counts_addresses(self):
        bounds=[[-8,9],[-9,8]];p=self.packet(1);q=self.packet()
        expected=[[x,y] for x in range(-8,10) for y in range(-9,9) if (y-x*x)%8==0 and (y-x)%4==0]
        self.assertEqual(intersection_population(p,bounds)['count'],len(expected))
        self.assertEqual(intersection_population(q,bounds)['count'],len(expected))
        actual=[]
        for i in range(len(expected)):
            z=intersection_select(p,bounds,i);actual.append(z)
            self.assertEqual(intersection_rank(p,bounds,z),i)
            self.assertEqual(intersection_select(q,bounds,i),z)
        self.assertEqual(sorted(actual),expected)
        with self.assertRaises(IndexError):intersection_select(p,bounds,len(expected))
        with self.assertRaises(ValueError):intersection_rank(p,bounds,[2,4])
        with self.assertRaises(ValueError):intersection_rank(p,bounds,[100,100])

    def test_huge_population_without_enumeration(self):
        p=self.packet(1);h=10**60;bounds=[[-h,h],[-h,h]]
        def axis(r):return (h-r)//8-(-h-1-r)//8
        expected=sum(axis(x)*axis(y) for x,y in self.packet()['roots'])
        self.assertEqual(intersection_population(p,bounds)['count'],expected)
        for i in (0,expected//2,expected-1):
            z=intersection_select(p,bounds,i);self.assertEqual(intersection_rank(p,bounds,z),i)

    def test_exact_simultaneous_source_scan(self):
        p=self.packet();bounds=[[-10,10],[-10,10]]
        self.assertEqual(intersection_scan(p,bounds)['points'],[[0,0],[1,1]])
        self.assertEqual(intersection_scan(p,bounds)['source_count'],2)
        with self.assertRaises(ValueError):intersection_scan(p,bounds,candidate_limit=0)

    def test_all_empty_factor_positions(self):
        impossible=atlas_packet([[1,0,0]],3,1)
        for factors in ([impossible,atlas_packet(Y,2,1)],
                        [atlas_packet(Y,2,1),impossible,atlas_packet(Y,5,1)],
                        [atlas_packet(Y,2,1),atlas_packet(Y,3,1),atlas_packet([[1,0,0]],5,1)]):
            p=intersect_atlases(factors,explicit_limit=1)
            self.assertTrue(verify_intersection(p));self.assertEqual(p['combination_count'],0)
            self.assertEqual(intersection_population(p,[[-3,4],[-3,4]])['count'],0)

    def test_corruption_is_rejected(self):
        p=self.packet()
        changes=[('modulus',16),('modulus',True),('combination_count',3),('roots',p['roots'][:-1]),
                 ('global_obstruction',True),('execution_verified',True),('global_height_bound',True),
                 ('complete_modular_cover',1),('representation','factored'),('explicit_limit',True),('unexpected',True)]
        for key,value in changes:
            q=copy.deepcopy(p);q[key]=value;self.assertFalse(verify_intersection(q),key)
        for change in ('partition','local_root','source','duplicate'):
            q=copy.deepcopy(p)
            if change=='partition':q['locals'][0]['constraint_ids']=[]
            elif change=='local_root':q['locals'][0]['roots'].pop()
            elif change=='source':q['constraints'][0]['terms'][0][0]+=1
            else:q['constraints'].append(q['constraints'][0])
            self.assertFalse(verify_intersection(q),change)
        for q in (None,{},[],{'schema':'pp-residue-atlas-intersection-factored/1','constraints':None}):
            self.assertFalse(verify_intersection(q))

    def test_budget_and_input_failures(self):
        for args in ([],[{}],None):
            with self.assertRaises(ValueError):intersect_atlases(args)
        with self.assertRaises(ValueError):intersect_atlases([atlas_packet(Y,2,1)],explicit_limit=True)
        p=intersect_atlases([atlas_packet(Y,2,1),atlas_packet(Y,3,1)])
        with self.assertRaises(ValueError):intersection_population(p,[[-100,100],[-100,100]],work_limit=0)
        for method in (intersection_population,intersection_scan):
            with self.assertRaises(ValueError):method(p,[[-100,100],[-100,100]],work_limit=1)
        bad=atlas_packet(Y,2,1);bad['roots'].pop()
        with self.assertRaises(ValueError):intersect_atlases([bad])
        with self.assertRaises(ValueError):intersection_contains(p,[True,0])
        with self.assertRaises(ValueError):native_intersection(intersect_atlases([atlas_packet(Y,2,6)]),[[0,1],[0,1]])

    def test_query_and_native_output(self):
        args={'atlases':[atlas_packet(PARABOLA,2,3),atlas_packet(LINE,2,2)]}
        p=dispatch(None,{'op':'intersect_residue_atlases_factored','args':args})
        self.assertTrue(dispatch(None,{'op':'verify_residue_atlas_intersection_factored','args':{'packet':p}})['valid'])
        r=dispatch(None,{'op':'residue_intersection_factored_scan','args':{'packet':p,'bounds':[[-2,2],[-2,2]]}})
        self.assertEqual(r['points'],[[0,0],[1,1]])
        source=native_intersection(p,[[-2,2],[-2,2]])
        self.assertIn('nested ',source);self.assertIn('points_complete',source)
        self.assertNotIn('native_decide',source);self.assertNotIn('sorry',source)

if __name__=='__main__':unittest.main()
