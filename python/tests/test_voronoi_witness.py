import copy
import unittest
from fractions import Fraction as Q
from unittest.mock import patch
from perfectpower.voronoi_certificate import produce, verify, transfer_piece, children, UNIT, SurfaceSpace


def tetrahedron(scale=1):
    return {'vertices':4,'triangles':[[0,2,1],[0,1,3],[0,3,2],[1,2,3]],
            'edge_lengths':[[a,b,str(scale)] for a in range(4) for b in range(a+1,4)]}


class VoronoiWitnessTests(unittest.TestCase):
    def setUp(self):
        self.mesh=tetrahedron()
        self.packet=produce(self.mesh,[0,1],[[0,1,0,0],[1,0,0,0]],3)

    def test_independent_checker(self):
        with patch('perfectpower.certified_voronoi.boundary_enclosure',side_effect=AssertionError('producer called')):
            self.assertTrue(verify(self.mesh,self.packet))
        self.assertTrue(any(p['site'] is not None for p in self.packet['pieces']))

    def test_leaf_coverage(self):
        for face in range(4):
            self.assertEqual(sum(Q(p['face_area_fraction']) for p in self.packet['pieces'] if p['face']==face),1)
        bad=copy.deepcopy(self.packet);bad['pieces'].pop()
        self.assertFalse(verify(self.mesh,bad))

    def test_overlaps_and_duplicates(self):
        bad=copy.deepcopy(self.packet);bad['pieces'].append(copy.deepcopy(bad['pieces'][0]))
        self.assertFalse(verify(self.mesh,bad))
        bad=copy.deepcopy(self.packet);leaf=copy.deepcopy(bad['pieces'][0])
        leaf['address'].append(0);leaf['barycentric_triangle']=[list(map(str,row)) for row in children(tuple(tuple(Q(x) for x in v) for v in leaf['barycentric_triangle']))[0]]
        leaf['face_area_fraction']=str(Q(leaf['face_area_fraction'])/4)
        bad['pieces'].append(leaf)
        self.assertFalse(verify(self.mesh,bad))

    def test_radius_upper_lower_and_winner_tampering(self):
        for key,value in [('radius_upper','-1'),('center_upper',['-1','-1']),('center_lower',['100','100'])]:
            bad=copy.deepcopy(self.packet);bad['pieces'][0][key]=value
            self.assertFalse(verify(self.mesh,bad))
        bad=copy.deepcopy(self.packet)
        piece=next(p for p in bad['pieces'] if p['site'] is not None)
        piece['site']=1-piece['site']
        self.assertFalse(verify(self.mesh,bad))

    def test_paths_and_gradients(self):
        bad=copy.deepcopy(self.packet);bad['paths'][0][1]=[1]
        self.assertFalse(verify(self.mesh,bad))
        bad=copy.deepcopy(self.packet);bad['fields'][0][1]='100'
        self.assertFalse(verify(self.mesh,bad))

    def test_witness_freedom(self):
        # The checker accepts conservative weaker bounds; it is not equality replay.
        bad=copy.deepcopy(self.packet)
        for p in bad['pieces']:
            p['site']=None;p['center_upper']=[str(Q(x)+1) for x in p['center_upper']]
            p['center_lower']=['0','0'];p['radius_upper']=str(Q(p['radius_upper'])+1)
        self.assertTrue(verify(self.mesh,bad))

    def test_closed_surface_validation(self):
        for mutate in (lambda m:m['triangles'].pop(),lambda m:m['triangles'][0].reverse(),
                       lambda m:m['edge_lengths'].append(m['edge_lengths'][0]),
                       lambda m:m['edge_lengths'][0].__setitem__(2,'3')):
            mesh=copy.deepcopy(self.mesh);mutate(mesh)
            self.assertFalse(verify(mesh,self.packet))

    def test_no_smooth_claim(self):
        bad=copy.deepcopy(self.packet);bad['smooth_curve_metric_certified']=True
        self.assertFalse(verify(self.mesh,bad))
        p=next(p for p in self.packet['pieces'] if p['site'] is not None)
        same=transfer_piece(p,1,1)
        self.assertEqual(same['winner_index'],self.packet['sites'].index(p['site']))
        self.assertFalse(same['comparison_proved'])
        self.assertIsNone(transfer_piece(p,Q(1,100),100)['winner_index'])
        for l,u in [(0,1),(2,1),(-1,1)]:
            with self.assertRaises(ValueError):transfer_piece(p,l,u)

    def test_empty_fields_and_zero_depth(self):
        packet=produce(self.mesh,[0,1],[],0)
        self.assertTrue(verify(self.mesh,packet))
        self.assertEqual(len(packet['pieces']),4)
        self.assertTrue(all(p['site'] is None for p in packet['pieces']))

    def test_scale_and_dense_sites(self):
        for scale in [Q(1,3),Q(7,2)]:
            mesh=tetrahedron(scale)
            packet=produce(mesh,[0,1,2,3],[[0,100,0,0]],2)
            self.assertTrue(verify(mesh,packet))

    def test_reject_shape_and_index_tampering(self):
        for key,value in [('sites',[0,True]),('depth',True),('paths',[]),('schema','other')]:
            bad=copy.deepcopy(self.packet);bad[key]=value
            self.assertFalse(verify(self.mesh,bad))
        bad=copy.deepcopy(self.packet);bad['pieces'][0]['barycentric_triangle'][0][0]='100'
        self.assertFalse(verify(self.mesh,bad))

    def test_reusable_surface_queries(self):
        space=SurfaceSpace(self.mesh,self.packet)
        first=space.point(0,[1,0,0])
        self.assertEqual(first['unique_winner'],0)
        self.assertEqual(first['possible_nearest_sites'],[0])
        first['lower'][0]='999'
        self.assertEqual(space.point(0,[1,0,0])['lower'][0],'0')
        middle=space.point(0,[Q(1,2),0,Q(1,2)])
        self.assertIsNone(middle['unique_winner'])
        self.assertEqual(middle['possible_nearest_sites'],[0,1])
        self.assertEqual(space.statistics()['certificate_checks'],1)
        self.assertEqual(space.statistics()['point_queries'],3)
        with self.assertRaises(ValueError):space.point(0,[1,1,0])
        with self.assertRaises(ValueError):space.point(-1,[1,0,0])

    def test_query_bounds_against_euclidean_chords(self):
        # Each regular tetrahedron face lies in a Euclidean plane. Its ambient
        # chord is a necessary lower bound; an in-face path is an upper witness.
        space=SurfaceSpace(self.mesh,self.packet)
        for a in range(9):
            for b in range(9-a):
                p=[Q(a,8),Q(b,8),Q(8-a-b,8)]
                query=space.point(0,p)
                for site,lo,hi in zip(query['sites'],query['lower'],query['upper']):
                    k=self.mesh['triangles'][0].index(site)
                    delta=[p[i]-int(i==k) for i in range(3)]
                    chord2=sum(x*x for x in delta)/2
                    # Ambient tetrahedron chords have squared norm sum(delta²)/2.
                    self.assertLessEqual(Q(lo)**2,chord2)
                    self.assertGreaterEqual(Q(hi)**2,chord2)

if __name__=='__main__': unittest.main()
