import copy
import unittest
from math import lcm
from perfectpower.residue_atlas import atlas_packet
from perfectpower.residue_atlas_product import product_packet
from perfectpower.residue_atlas_intersection import (
    generalized_crt, intersect_atlases, verify_intersection,
    intersection_population, intersection_rank, intersection_select)


class IntersectionTests(unittest.TestCase):
    def test_crt_exhaustive(self):
        for m in range(1, 17):
            for n in range(1, 17):
                for a in range(m):
                    for b in range(n):
                        expected = next((x for x in range(lcm(m,n))
                                         if x % m == a and x % n == b), None)
                        self.assertEqual(generalized_crt(a,b,m,n), expected)

    def test_distinct_sources_shared_prime(self):
        # x=y mod 4, x=-y mod 8: compatibility reduces 32 pairs to 4.
        p = intersect_atlases([atlas_packet([[1,1,0],[-1,0,1]],2,2),
                              atlas_packet([[1,1,0],[1,0,1]],2,3)])
        expected = [[x,y] for x in range(8) for y in range(8)
                    if (x-y)%4 == 0 and (x+y)%8 == 0]
        self.assertEqual(p['roots'], expected)
        self.assertEqual(p['modulus'], 8)
        self.assertEqual(p['stages'][-1]['compatible_count'], 4)
        self.assertTrue(verify_intersection(p))
        bounds = [[-13,17],[-9,12]]
        points = sorted(([x,y] for x in range(-13,18) for y in range(-9,13)
                         if (x-y)%4 == 0 and (x+y)%8 == 0),
                        key=lambda z:(z[0]%8,z[1]%8,z[0],z[1]))
        self.assertEqual(intersection_population(p,bounds),len(points))
        for i, z in enumerate(points):
            self.assertEqual(intersection_select(p,bounds,i),z)
            self.assertEqual(intersection_rank(p,bounds,z),i)
        with self.assertRaises(IndexError): intersection_select(p,bounds,len(points))

    def test_shared_composite_products(self):
        f = [[1,1,0],[-1,0,1]]; h = [[1,1,0],[1,0,1]]
        p = intersect_atlases([product_packet(f,[[2,2],[3,1]]),
                              product_packet(h,[[2,3],[5,1]])])
        self.assertEqual(p['modulus'],120)
        self.assertEqual(p['roots'],[[x,y] for x in range(120) for y in range(120)
                                    if (x-y)%12 == 0 and (x+y)%40 == 0])
        rev = intersect_atlases(list(reversed(p['inputs'])))
        self.assertEqual(rev['roots'],p['roots'])

    def test_empty_obstruction_and_tampering(self):
        p = intersect_atlases([atlas_packet([[1,1,0]],2,1),
                              atlas_packet([[1,1,0],[-1,0,0]],2,1)])
        self.assertTrue(p['global_obstruction'])
        self.assertEqual(p['roots'],[])
        self.assertEqual(intersection_population(p,[[-10**30,10**30]]*2),0)
        for field, value in [('modulus',4),('global_obstruction',1),('roots',[[0,0]])]:
            q = copy.deepcopy(p); q[field] = value
            self.assertFalse(verify_intersection(q))
        q = copy.deepcopy(p); q['extra'] = True
        self.assertFalse(verify_intersection(q))

    def test_query_operations(self):
        from perfectpower.query_service import dispatch
        a = atlas_packet([[1,1,0]],2,1)
        p = dispatch(None, {'op':'intersect_residue_atlases','args':{'inputs':[a]}})
        self.assertEqual(p['schema'],'pp-residue-atlas-intersection/1')
        self.assertEqual(dispatch(None, {'op':'verify_residue_atlas_intersection',
                                       'args':{'packet':p}})['valid'],True)
        self.assertEqual(dispatch(None, {'op':'residue_intersection_population',
                         'args':{'packet':p,'bounds':[[0,3],[0,3]]}}),8)

    def test_budget_and_negative_crt(self):
        a = atlas_packet([[1,1,0],[-1,0,1]],2,3)
        with self.assertRaises(ValueError): intersect_atlases([a,a],work_limit=1)
        self.assertEqual(generalized_crt(-1,5,4,6),11)
        self.assertIsNone(generalized_crt(0,1,4,6))
        with self.assertRaises(ValueError): generalized_crt(True,0,4,6)
        p = intersect_atlases([a,a])
        self.assertEqual(p['roots'],a['roots'])
        self.assertGreater(intersection_population(p,[[-10**30,10**30]]*2),10**59)

if __name__ == '__main__': unittest.main()
