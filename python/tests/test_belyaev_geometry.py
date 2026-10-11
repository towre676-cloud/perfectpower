import unittest,random
from fractions import Fraction as Q
from copy import deepcopy
from heapq import heappop,heappush
from perfectpower.belyaev_geometry import *
from perfectpower.polygon_routing import route,segment_visibility,check_route
from perfectpower.geometry_lean import compile_isometry,compile_triangulation_area
from perfectpower.divisor_square import WorkLimit


class IncidenceAndCongruence(unittest.TestCase):
    def test_lines_and_strict_between(self):
        self.assertEqual(line_through([0,0],[1,1]),[1,-1,0])
        self.assertEqual(line_through([2,2],['1/2','1/2']),[1,-1,0])
        self.assertEqual(meet_lines([1,-1,0],[1,1,-2]),{'kind':'POINT','point':['1','1']})
        self.assertEqual(meet_lines([1,0,0],[2,0,0])['kind'],'COINCIDENT')
        self.assertEqual(meet_lines([1,0,0],[1,0,1])['kind'],'PARALLEL')
        self.assertTrue(between([0,0],['1/2','1/2'],[1,1]))
        self.assertFalse(between([0,0],[0,0],[1,1]))
        self.assertTrue(between([0,0],[0,0],[0,0],strict=False))
        with self.assertRaises(ValueError):line_through([0,0],[0,0])
        with self.assertRaises(ValueError):line_through([0.0,0],[1,0])

    def test_rational_rotations_and_reflections(self):
        source=[[0,0],[3,0],[0,4],[2,1]]
        for matrix in [[['3/5','-4/5'],['4/5','3/5']],[['3/5','4/5'],['4/5','-3/5']]]:
            transform={'matrix':matrix,'translation':['7/3','-2/7']}
            target=[apply_isometry(transform,p) for p in source]
            fit=fit_isometries(source,target)
            self.assertEqual(fit['status'],'CONGRUENT');self.assertEqual(len(fit['transforms']),1)
            self.assertEqual(fit['transforms'][0]['matrix'],matrix)
            for a in source:
                for b in source:
                    self.assertEqual(dot(sub(point(a),point(b)),sub(point(a),point(b))),dot(sub(apply_isometry(transform,a),apply_isometry(transform,b)),sub(apply_isometry(transform,a),apply_isometry(transform,b))))
            self.assertIn('distance_all_inputs',compile_isometry(fit['transforms'][0])['source'])
        target[2]=(target[2][0]+Q(1,1000000),target[2][1])
        self.assertEqual(fit_isometries(source,target)['status'],'NOT_CONGRUENT')

    def test_degenerate_congruence_is_not_overclaimed(self):
        self.assertEqual(len(fit_isometries([[0,0],[1,0]],[[2,2],[2,3]])['transforms']),2)
        p=fit_isometries([[0,0],[0,0]],[[2,2],[2,2]])
        self.assertEqual(p['status'],'UNDERDETERMINED');self.assertEqual(p['transforms'],[])
        self.assertEqual(fit_isometries([[0,0],[0,0]],[[2,2],[2,3]])['status'],'NOT_CONGRUENT')
        with self.assertRaises(ValueError):apply_isometry({'matrix':[[2,0],[0,1]],'translation':[0,0]},[1,2])

    def test_circumcircle_and_orientation_independent_incircle(self):
        r=random.Random(7201)
        for _ in range(100):
            triangle=[[r.randrange(-10,11),r.randrange(-10,11)] for _ in range(3)]
            if not orientation(*triangle):continue
            circle=circumcircle(*triangle);center=point(circle['center']);radius=Q(circle['radius_squared'])
            for p in triangle:self.assertEqual(dot(sub(point(p),center),sub(point(p),center)),radius)
            p=[r.randrange(-10,11),r.randrange(-10,11)];dist=dot(sub(point(p),center),sub(point(p),center))
            expected='INSIDE' if dist<radius else 'OUTSIDE' if dist>radius else 'ON'
            self.assertEqual(incircle(*triangle,p)['kind'],expected)
            self.assertEqual(incircle(*triangle[::-1],p)['kind'],expected)
        with self.assertRaises(ValueError):circumcircle([0,0],[1,1],[2,2])

    def test_incircle_at_binary64_resolution_boundary(self):
        n=2**60;p=[n,n-1]
        self.assertEqual(incircle([0,0],[n,0],[0,n],p)['kind'],'INSIDE')
        center=float(n)/2
        self.assertEqual((float(p[0])-center)**2+(float(p[1])-center)**2,float(n)**2/2)


class PolygonTests(unittest.TestCase):
    rectangle=[[0,0],[4,0],[4,3],[0,3]]
    concave=[[0,0],[4,0],[4,4],[2,2],[0,4]]
    def test_simplicity_touch_overlap_and_degeneracy(self):
        self.assertTrue(polygon_structure(self.rectangle)['simple'])
        for p in [[[0,0],[2,2],[0,2],[2,0]],[[0,0],[2,0],[1,0],[1,1]],[[0,0],[2,0],[0,0],[0,1]],[[0,0],[1,0],[2,0]]]:
            self.assertFalse(polygon_structure(p)['simple'])
            with self.assertRaises(ValueError):triangulate(p)
        self.assertTrue(polygon_structure([[0,0],[2,0],[4,0],[4,3],[0,3]])['simple'])
        with self.assertRaises(WorkLimit):triangulate(self.concave,work_limit=1)

    def test_triangulation_centroid_and_winding(self):
        for polygon in [self.rectangle,self.concave,self.concave[::-1],[[0,0],[2,0],[4,0],[4,3],[0,3]],[[0,0],['1/3',0],['1/3','1/7'],[0,'1/7']]]:
            packet=triangulate(polygon);self.assertTrue(check_triangulation(packet))
            self.assertEqual(len(packet['triangles']),len(packet['normalized_vertices'])-2)
            for tri in packet['triangles']:
                center=[sum(Q(v[i]) for v in tri)/3 for i in range(2)]
                self.assertEqual(locate_point(polygon,center),'INSIDE')
            self.assertIn('source_polygon_area',compile_triangulation_area(packet)['source'])
        self.assertEqual(polygon_centroid(self.rectangle),{'area':'12','centroid':['2','3/2'],'scope':'uniform filled polygon centroid; may lie outside a concave polygon'})
        self.assertEqual(locate_point(self.concave,[2,3]),'OUTSIDE')
        self.assertEqual(locate_point(self.concave,[2,2]),'BOUNDARY')
        bad=deepcopy(triangulate(self.concave));bad['triangles'].pop()
        with self.assertRaises(ValueError):check_triangulation(bad)

    def test_grid_partition_independent_triangle_coverage(self):
        for polygon in [self.concave,[[0,0],[5,0],[5,1],[1,1],[1,4],[0,4]],[[0,0],[6,0],[6,5],[4,5],[4,2],[2,2],[2,5],[0,5]]]:
            triangles=triangulate(polygon)['triangles']
            for x in range(-2,15):
                for y in range(-2,13):
                    p=[Q(x,2),Q(y,2)]
                    inside=locate_point(polygon,p)!='OUTSIDE'
                    self.assertEqual(any(triangle_contains(*tri,p) for tri in triangles),inside)
                    self.assertLessEqual(sum(triangle_contains(*tri,p,boundary=False) for tri in triangles),1)

    def test_voronoi_mesh_area_centroid_and_duplicate_ties(self):
        from perfectpower.euclid_geometry import nearest_sites
        r=random.Random(301)
        for _ in range(15):
            sites={str(i):[r.randrange(-5,6),r.randrange(-5,6)] for i in range(5)}
            sites['duplicate']=sites['0'];p=voronoi_mesh(sites,[[-3,-3],[3,3]])
            self.assertEqual(p['unique_cell_area'],'36')
            self.assertEqual(p['mesh']['duplicate'],p['mesh']['0'])
            for name,cell in p['mesh'].items():
                if cell['dimension']==2:self.assertIn(name,nearest_sites(sites,cell['centroid'])['sites'])
        with self.assertRaises(WorkLimit):voronoi_mesh({'a':[0,0]},[[0,0],[1,1]],work_limit=1)

    def test_rigid_voronoi_transport_preserves_nearest_sites(self):
        from perfectpower.euclid_geometry import voronoi_cells,nearest_sites
        sites={'a':[0,0],'b':[2,0],'c':[1,2],'duplicate':[0,0]}
        base=voronoi_cells(sites,[[-1,-1],[3,3]])
        for matrix in [[['3/5','-4/5'],['4/5','3/5']],[['3/5','4/5'],['4/5','-3/5']]]:
            transform={'matrix':matrix,'translation':['7/3','-2/7']};image=transport_voronoi(base,transform)
            for name,cell in image['cells'].items():
                for p in cell['vertices']:
                    self.assertIn(name,nearest_sites(image['sites'],p)['sites'])
                    for h in cell['inequalities']:self.assertLessEqual(dot(point(h['normal']),point(p)),Q(h['bound']))
                if len(cell['vertices'])>=3:
                    self.assertEqual(abs(signed_area2(list(map(point,cell['vertices'])))),abs(signed_area2(list(map(point,base['cells'][name]['vertices'])))))
        bad=deepcopy(base);bad['cells']['a']['vertices'].pop()
        with self.assertRaises(ValueError):transport_voronoi(bad,transform)


class RoutingTests(unittest.TestCase):
    obstacle=[[0,0],[2,0],[2,2],[0,2]]
    def test_contact_boundary_crossing_and_concavity(self):
        for a,b,visible in [([-1,1],[3,1],False),([-1,0],[3,0],True),([-1,-1],[0,0],True),([0,0],[2,2],False),([0,0],[0,2],True),([0,0],[0,0],True)]:
            self.assertEqual(segment_visibility([self.obstacle],a,b)['visible'],visible)
        concave=PolygonTests.concave
        self.assertFalse(segment_visibility([concave],[0,0],[4,4])['visible'])
        self.assertTrue(segment_visibility([concave],[0,4],[4,4])['visible'])

    def test_exact_route_and_independent_bellman_ford(self):
        for obstacles,start,end in [([self.obstacle],[-1,1],[3,1]),([],[0,0],[3,4]),([self.obstacle],[0,0],[0,0]),([self.obstacle,[[3,1],[4,1],[4,3],[3,3]]],[-1,1],[5,2])]:
            p=route(obstacles,start,end);self.assertTrue(check_route(p));self.assertEqual(p['status'],'ROUTE')
            for a,b in zip(p['path'],p['path'][1:]):self.assertTrue(segment_visibility(obstacles,a,b)['visible'])
            # Independently solve the saved complete graph by repeated relaxation.
            distances={0:Q(0)}
            for _ in p['vertices']:
                for a,b,w in p['edges']:
                    w=Q(w)
                    for u,v in [(a,b),(b,a)]:
                        if u in distances and (v not in distances or distances[u]+w<distances[v]):distances[v]=distances[u]+w
            target=p['vertices'].index(p['end']);self.assertEqual(Q(p['cost']),distances[target])
        p=route([self.obstacle],[-1,1],[3,1]);self.assertEqual(p['cost'],'6');self.assertGreater(len(p['path']),2)
        bad=deepcopy(p);bad['cost']='4'
        with self.assertRaises(ValueError):check_route(bad)

    def test_invalid_and_resource_limited_routes(self):
        with self.assertRaises(ValueError):route([self.obstacle],[1,1],[3,1])
        with self.assertRaises(WorkLimit):route([self.obstacle],[-1,1],[3,1],vertex_limit=2)
        with self.assertRaises(WorkLimit):route([self.obstacle],[-1,1],[3,1],work_limit=10)
        with self.assertRaises(ValueError):route([],[-1.0,1],[3,1])
        from perfectpower.belyaev_cli import dispatch
        self.assertEqual(dispatch('route',{'obstacles':[self.obstacle],'start':[-1,1],'end':[3,1]})['cost'],'6')

    def test_unreachable_enclosed_component(self):
        ring=[ [[-3,1],[3,1],[3,3],[-3,3]], [[-3,-3],[3,-3],[3,-1],[-3,-1]],
               [[-3,-3],[-1,-3],[-1,3],[-3,3]], [[1,-3],[3,-3],[3,3],[1,3]] ]
        p=route(ring,[0,0],[5,0]);self.assertEqual(p['status'],'UNREACHABLE');self.assertIsNone(p['cost'])


if __name__=='__main__':unittest.main()
