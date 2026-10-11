import unittest
from copy import deepcopy
from fractions import Fraction as Q
import random
from unittest.mock import patch
from perfectpower.geometry_certificates import (
    certify_mesh,check_mesh_certificate,compile_mesh_certificate,
    certify_route,check_route_certificate,compile_route_certificate,digest)
from perfectpower.belyaev_geometry import triangulate,apply_isometry,triangle_contains,locate_point
from perfectpower.polygon_routing import route
from perfectpower.divisor_square import WorkLimit

SQUARE=[[0,0],[4,0],[4,4],[0,4]]
FAN=[[[0,0],[4,0],[2,2]],[[4,0],[4,4],[2,2]],[[4,4],[0,4],[2,2]],[[0,4],[0,0],[2,2]]]
OBSTACLE=[[0,0],[2,0],[2,2],[0,2]]
RING=[[[-3,1],[3,1],[3,3],[-3,3]],[[-3,-3],[3,-3],[3,-1],[-3,-1]],
      [[-3,-3],[-1,-3],[-1,3],[-3,3]],[[1,-3],[3,-3],[3,3],[1,3]]]


class MeshCertificates(unittest.TestCase):
    def test_accepts_external_fan_without_ear_algorithm(self):
        with patch('perfectpower.belyaev_geometry.triangulate',side_effect=AssertionError('optimizer forbidden')):
            packet=certify_mesh(SQUARE,FAN)
            self.assertTrue(check_mesh_certificate(packet))
        self.assertEqual(packet['area'],'16');self.assertEqual(len(packet['separators']),6)
        self.assertTrue(any(a['source_coefficient']==0 for a in packet['boundary_atoms']))
        proof=compile_mesh_certificate(packet)
        self.assertIn('boundary_counts',proof['source']);self.assertIn('separation_0_3',proof['source'])
        self.assertFalse(proof['kernel_checked'])

    def test_accepts_t_junction_and_subdivided_boundary(self):
        # Lower half has one triangle, upper half is split at the diagonal midpoint.
        mesh=[[[0,0],[4,0],[4,4]],[[0,0],[2,2],[0,4]],[[2,2],[4,4],[0,4]]]
        packet=certify_mesh(SQUARE,mesh);self.assertTrue(check_mesh_certificate(packet))
        # A source collinear boundary vertex need not appear in any triangle.
        packet=certify_mesh([[0,0],[2,0],[4,0],[4,4],[0,4]],FAN)
        self.assertEqual(packet['area'],'16')

    def test_accepts_both_diagonals_and_cw_polygon(self):
        for mesh in [[[[0,0],[4,0],[4,4]],[[0,0],[4,4],[0,4]]],
                     [[[0,0],[4,0],[0,4]],[[4,0],[4,4],[0,4]]]]:
            self.assertEqual(certify_mesh(SQUARE[::-1],mesh)['area'],'16')

    def test_rejects_area_balanced_overlap_and_gap(self):
        # Both triangles have area 8; sum equals square but interiors overlap.
        bad=[[[0,0],[4,0],[4,4]],[[0,0],[4,0],[0,4]]]
        with self.assertRaisesRegex(ValueError,'overlap'):certify_mesh(SQUARE,bad)
        # Equal area replacement outside the source: no overlap, wrong boundary.
        bad=[[[0,0],[4,0],[4,4]],[[4,0],[8,0],[8,4]]]
        with self.assertRaisesRegex(ValueError,'boundary'):certify_mesh(SQUARE,bad)

    def test_rejects_holes_reversal_degeneracy_and_tampering(self):
        for mesh in [FAN[:-1],FAN+[FAN[0]],[[[0,0],[4,0],[2,0]]],[[[0,0],[0,4],[4,0]]],[]]:
            with self.assertRaises(ValueError):certify_mesh(SQUARE,mesh)
        p=certify_mesh(SQUARE,FAN)
        for key,value in [('area','17'),('separators',[]),('boundary_atoms',[])]:
            bad=deepcopy(p);bad[key]=value
            with self.assertRaises(ValueError):check_mesh_certificate(bad)

    def test_concave_meshes_and_rational_isometries(self):
        polygons=[[[0,0],[5,0],[5,1],[1,1],[1,4],[0,4]],
                  [[0,0],[6,0],[6,5],[4,5],[4,2],[2,2],[2,5],[0,5]]]
        transform={'matrix':[['3/5','-4/5'],['4/5','3/5']],'translation':['7/3','-2/7']}
        for polygon in polygons:
            triangles=triangulate(polygon)['triangles'];p=certify_mesh(polygon,triangles)
            image=lambda v:apply_isometry(transform,v)
            q=certify_mesh(list(map(image,polygon)),[list(map(image,t)) for t in triangles])
            self.assertEqual(p['area'],q['area'])
            for x in range(-2,15):
                for y in range(-2,13):
                    point=[Q(x,2),Q(y,2)]
                    self.assertEqual(any(triangle_contains(*t,point) for t in p['triangles']),locate_point(polygon,point)!='OUTSIDE')

    def test_random_rational_steiner_fans(self):
        rng=random.Random(10211)
        for _ in range(30):
            center=[Q(rng.randrange(1,40),10),Q(rng.randrange(1,40),10)]
            fan=[[SQUARE[i],SQUARE[(i+1)%4],center] for i in range(4)]
            p=certify_mesh(SQUARE,fan);self.assertEqual(p['area'],'16')

    def test_limits_and_exact_inputs(self):
        for limits in [{'work_limit':1},{'triangle_limit':3},{'vertex_limit':4}]:
            with self.assertRaises(WorkLimit):certify_mesh(SQUARE,FAN,**limits)
        with self.assertRaises(ValueError):certify_mesh(SQUARE,FAN,triangle_limit=True)
        bad=deepcopy(FAN);bad[0][2]=[2.0,2]
        with self.assertRaises(ValueError):certify_mesh(SQUARE,bad)


class VoronoiCertificates(unittest.TestCase):
    def test_duplicate_and_degenerate_cells_and_corrupt_moments(self):
        from perfectpower.belyaev_geometry import voronoi_mesh
        from perfectpower.geometry_certificates import certify_voronoi_mesh
        p=voronoi_mesh({'a':[0,0],'b':[2,0],'duplicate':[0,0],'far':[100,100]},[[-1,-1],[3,3]])
        with patch('perfectpower.belyaev_geometry.triangulate',side_effect=AssertionError('ear clipping forbidden')):
            c=certify_voronoi_mesh(p)
        self.assertEqual(c['unique_cell_area'],'16')
        self.assertEqual(c['unique_cell_references']['duplicate'],'a')
        self.assertIsNone(c['unique_cell_references']['far'])
        for key,value in [('area','99'),('centroid',['0','0'])]:
            bad=deepcopy(p);bad['mesh']['a'][key]=value
            with self.assertRaises(ValueError):certify_voronoi_mesh(bad)
        bad=deepcopy(p);bad['unique_cell_area']='32'
        with self.assertRaises(ValueError):certify_voronoi_mesh(bad)
        with self.assertRaises(WorkLimit):certify_voronoi_mesh(p,work_limit=1)

    def test_external_alternative_mesh_and_random_diagrams(self):
        from perfectpower.belyaev_geometry import voronoi_mesh
        from perfectpower.geometry_certificates import certify_voronoi_mesh
        p=voronoi_mesh({'a':[0,0]},[[0,0],[4,4]])
        p['mesh']['a']['triangles']=FAN
        self.assertEqual(certify_voronoi_mesh(p)['unique_cell_area'],'16')
        rng=random.Random(1411)
        for _ in range(15):
            p=voronoi_mesh({str(i):[rng.randrange(-5,6),rng.randrange(-5,6)] for i in range(5)},[[-3,-3],[3,3]])
            self.assertEqual(certify_voronoi_mesh(p)['unique_cell_area'],'36')


class RouteCertificates(unittest.TestCase):
    def test_route_dual_checks_without_optimizer(self):
        p=route([OBSTACLE],[-1,1],[3,1]);c=certify_route(p)
        with patch('perfectpower.polygon_routing.route',side_effect=AssertionError('search forbidden')), \
             patch('perfectpower.geometry_certificates.heappop',side_effect=AssertionError('search forbidden')):
            self.assertTrue(check_route_certificate(p,c))
        source=compile_route_certificate(p,c)['source']
        self.assertIn('no_cheaper_walk',source);self.assertIn('retained_path',source)

    def test_accepts_dual_offset_without_requiring_canonical_distances(self):
        p=route([OBSTACLE],[-1,1],[3,1]);c=certify_route(p)
        c['potentials']=[str(Q(v)+Q(7,3)) for v in c['potentials']]
        self.assertTrue(check_route_certificate(p,c))
        self.assertEqual(compile_route_certificate(p,c)['denominator'],3)

    def test_cut_and_disconnected_potentials(self):
        p=route(RING,[0,0],[5,0]);c=certify_route(p)
        self.assertTrue(check_route_certificate(p,c));self.assertNotIn(1,c['reachable'])
        self.assertIn('no_route',compile_route_certificate(p,c)['source'])
        c['reachable'].append(1);c['reachable'].sort()
        with self.assertRaises(ValueError):check_route_certificate(p,c)

    def test_corrupt_dual_path_cost_and_source(self):
        p=route([OBSTACLE],[-1,1],[3,1]);c=certify_route(p)
        bad=deepcopy(c);bad['potentials'][1]='7'
        with self.assertRaises(ValueError):check_route_certificate(p,bad)
        bad=deepcopy(c);bad['potentials'][1]=6.0
        with self.assertRaises(ValueError):check_route_certificate(p,bad)
        for key,value in [('cost','4'),('path_indices',[0,1]),('edges',p['edges'][:-1]),('vertices',p['vertices'][:-1])]:
            bad=deepcopy(p);bad[key]=value;proof=deepcopy(c);proof['source_sha256']=digest(bad)
            with self.assertRaises(ValueError):check_route_certificate(bad,proof)
        bad=deepcopy(c);bad['source_sha256']='0'*64
        with self.assertRaises(ValueError):check_route_certificate(p,bad)

    def test_zero_length_rational_and_alternative_equal_cost_path(self):
        for start,end in [([0,0],[0,0]),(['1/3','2/7'],['4/3','9/7'])]:
            p=route([],start,end);c=certify_route(p)
            self.assertTrue(check_route_certificate(p,c));self.assertIn('no_cheaper_walk',compile_route_certificate(p,c)['source'])
        p=route([OBSTACLE],[-1,1],[3,1]);p['path_indices']=[0,5,4,1]
        p['path']=[p['vertices'][i] for i in p['path_indices']]
        self.assertTrue(check_route_certificate(p,certify_route(p)))

    def test_grid_endpoints_and_bellman_ford_oracle(self):
        rng=random.Random(9007)
        for _ in range(30):
            start=[-rng.randrange(1,5),Q(rng.randrange(-2,7),2)]
            end=[rng.randrange(3,7),Q(rng.randrange(-2,7),2)]
            p=route([OBSTACLE],start,end);c=certify_route(p)
            distances={0:Q(0)}
            for _ in p['vertices']:
                for u,v,w in p['edges']:
                    for a,b in [(u,v),(v,u)]:
                        if a in distances:distances[b]=min(distances.get(b,distances[a]+Q(w)),distances[a]+Q(w))
            self.assertEqual(Q(p['cost']),distances[1]);self.assertTrue(check_route_certificate(p,c))

    def test_limits_and_cli(self):
        p=route([OBSTACLE],[-1,1],[3,1]);c=certify_route(p)
        with self.assertRaises(WorkLimit):check_route_certificate(p,c,work_limit=1)
        with self.assertRaises(WorkLimit):check_route_certificate(p,c,vertex_limit=2)
        from perfectpower.belyaev_cli import dispatch
        result=dispatch('route-proof',{'obstacles':[OBSTACLE],'start':[-1,1],'end':[3,1]})
        self.assertEqual(result['route']['cost'],'6');self.assertIn('no_cheaper_walk',result['proof']['source'])
        result=dispatch('mesh-proof',{'vertices':SQUARE,'triangles':FAN})
        self.assertIn('boundary_counts',result['source'])

if __name__=='__main__':unittest.main()
