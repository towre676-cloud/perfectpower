import copy
from fractions import Fraction as Q
import random
import unittest
from perfectpower.geometry_admission import segment_evidence, compile_geometric_route_certificate, _lines
from perfectpower.geometry_certificates import certify_route, certify_mesh, digest
from perfectpower.polygon_routing import route, segment_visibility
from perfectpower.belyaev_geometry import _locate
from perfectpower.euclid_geometry import point, segment_intersection
from perfectpower.divisor_square import WorkLimit

SQUARE=[[0,0],[2,0],[2,2],[0,2]]
CONCAVE=[[0,0],[6,0],[6,5],[4,5],[4,2],[2,2],[2,5],[0,5]]

class GeometryAdmission(unittest.TestCase):
    def assertEvidence(self,obstacles,a,b,expected):
        evidence=segment_evidence(obstacles,a,b)
        self.assertEqual(evidence['status']=='FREE',expected)
        self.assertEqual(segment_visibility(obstacles,a,b)['visible'],expected)
        a,b=map(point,(a,b));polygons=[list(map(point,p)) for p in obstacles]
        if not expected:
            t=Q(evidence['parameter']);self.assertTrue(0<=t<=1)
            p=tuple(x+t*(y-x) for x,y in zip(a,b))
            self.assertTrue(any(_locate(poly,p)=='INSIDE' for poly in polygons))
        else:
            cells=[tuple(map(Q,c)) for c in evidence['cells']]
            self.assertEqual(cells[0][0],0);self.assertEqual(cells[-1][1],1)
            for i,(lo,hi) in enumerate(cells):
                self.assertLess(lo,hi)
                if i:self.assertEqual(cells[i-1][1],lo)
                for slope,offset in _lines(polygons,a,b):
                    self.assertGreaterEqual((slope*lo+offset)*(slope*hi+offset),0)
                for t in (lo,(lo+hi)/2,hi):
                    p=tuple(x+t*(y-x) for x,y in zip(a,b))
                    self.assertFalse(any(_locate(poly,p)=='INSIDE' for poly in polygons))

    def test_concave_notch_and_crossing(self):
        self.assertEvidence([CONCAVE],[3,3],[3,6],True)
        self.assertEvidence([CONCAVE],[1,4],[5,4],False)
        self.assertEvidence([CONCAVE],[2,5],[4,5],True)

    def test_tangent_vertex_boundary_and_overlap(self):
        self.assertEvidence([SQUARE],[-1,1],[1,-1],True)
        self.assertEvidence([SQUARE],[-1,0],[3,0],True)
        self.assertEvidence([SQUARE],[0,0],[2,2],False)
        self.assertEvidence([SQUARE,SQUARE],[0,0],[0,2],True)
        self.assertEvidence([SQUARE,[[1,0],[3,0],[3,2],[1,2]]],[0,0],[3,0],True)
        self.assertEvidence([SQUARE,[[1,0],[3,0],[3,2],[1,2]]],[-1,1],[4,1],False)

    def test_constant_segments(self):
        self.assertEvidence([SQUARE],[0,1],[0,1],True)
        self.assertEvidence([SQUARE],[1,1],[1,1],False)
        self.assertEvidence([],['1/3','2/7'],['1/3','2/7'],True)

    def test_rational_and_reversed(self):
        for a,b in [(['-1/7','1/3'],['17/7','1/3']),(['-1/7','0'],['17/7','0'])]:
            expected=segment_visibility([SQUARE],a,b)['visible']
            self.assertEvidence([SQUARE],a,b,expected)
            self.assertEvidence([list(reversed(SQUARE))],b,a,expected)

    def test_exact_regression_campaign(self):
        rng=random.Random(9184)
        for obstacles in ([SQUARE],[CONCAVE],[SQUARE,[[1,0],[3,0],[3,2],[1,2]]]):
            for _ in range(60):
                a=[str(Q(rng.randrange(-8,25),3)) for _ in range(2)]
                b=[str(Q(rng.randrange(-8,25),3)) for _ in range(2)]
                self.assertEvidence(obstacles,a,b,segment_visibility(obstacles,a,b)['visible'])

    def test_complete_source_binding(self):
        packet=route([SQUARE],[-1,1],[3,1]);cert=certify_route(packet)
        proof=compile_geometric_route_certificate(packet,cert)
        self.assertEqual(len(proof['pair_evidence']),len(packet['vertices'])*(len(packet['vertices'])-1))
        self.assertIn('geometric_complete',proof['source']);self.assertIn('source_edges',proof['source'])
        self.assertIn('sourceObstacles.flatten).eraseDups',proof['source'])
        self.assertFalse(proof['kernel_checked'])
        self.assertIn('no_cheaper_geometric_walk',proof['source'])

    def test_missing_extra_wrong_weight_and_vertex_graphs(self):
        original=route([SQUARE],[-1,1],[3,1])
        for kind in ('missing','extra','weight','vertex','source'):
            packet=copy.deepcopy(original)
            if kind=='missing':packet['edges'].pop()
            elif kind=='extra':packet['edges'].append([0,1,'4'])
            elif kind=='weight':packet['edges'][0][2]='999'
            elif kind=='vertex':packet['vertices'].append(['9','9'])
            else:packet['obstacles'][0][0]=['1','0']
            cert=certify_route(original);cert['source_sha256']=digest(packet)
            with self.assertRaises(ValueError):compile_geometric_route_certificate(packet,cert)

    def test_disconnected_ring(self):
        ring=[[[-3,1],[3,1],[3,3],[-3,3]],[[-3,-3],[3,-3],[3,-1],[-3,-1]],
              [[-3,-3],[-1,-3],[-1,3],[-3,3]],[[1,-3],[3,-3],[3,3],[1,3]]]
        packet=route(ring,[0,0],[5,0]);self.assertEqual(packet['status'],'UNREACHABLE')
        proof=compile_geometric_route_certificate(packet,certify_route(packet))
        self.assertIn('no_geometric_route',proof['source'])

    def test_steiner_and_disconnected_mesh_rejection(self):
        square=[[0,0],[4,0],[4,4],[0,4]]
        mesh=[[[0,0],[4,0],[2,2]],[[4,0],[4,4],[2,2]],[[4,4],[0,4],[2,2]],[[0,4],[0,0],[2,2]]]
        self.assertEqual(certify_mesh(square,mesh)['area'],'16')
        with self.assertRaises(ValueError):certify_mesh(square,mesh[:-1])
        with self.assertRaises(ValueError):certify_mesh(square,[mesh[0],[[8,8],[12,8],[12,12]]])

    def test_intersection_adversaries(self):
        self.assertEqual(segment_intersection([0,0],[4,0],[1,0],[3,0])['kind'],'OVERLAP')
        self.assertEqual(segment_intersection([0,0],[0,0],[0,0],[1,0])['kind'],'TOUCH')
        self.assertEqual(segment_intersection([0,0],[4,4],[0,4],[4,0])['kind'],'PROPER')
        self.assertEqual(segment_intersection([0,0],[1,0],[2,0],[3,0])['kind'],'DISJOINT')

    def test_budget_rejects_without_partial_acceptance(self):
        with self.assertRaises(WorkLimit):segment_evidence([SQUARE],[-1,1],[3,1],work_limit=1)
        packet=route([SQUARE],[-1,1],[3,1])
        with self.assertRaises(WorkLimit):compile_geometric_route_certificate(packet,certify_route(packet),work_limit=1)

    def test_refinement_pointwise_coverage_emitter(self):
        from perfectpower.geometry_admission import compile_refinement_mesh_certificate
        polygon=[[0,0],[6,0],[0,6]]
        mesh=[[[0,0],[6,0],[3,3]],[[0,0],[3,3],[0,6]]]
        packet=certify_mesh(polygon,mesh)
        proof=compile_refinement_mesh_certificate(packet,[{'triangle':0,'parameter':'1/2'}])
        self.assertIn('refinement_coverage',proof['source'])
        for trace in ([{'triangle':0,'parameter':'1/3'}],[{'triangle':0,'parameter':'0'}],
                      [{'triangle':0,'parameter':0.5}],[{'triangle':3,'parameter':'1/2'}]):
            with self.assertRaises(ValueError):compile_refinement_mesh_certificate(packet,trace)

    def test_contact_certificates(self):
        from perfectpower.geometry_admission import compile_boundary_contact_certificate
        for a,b,status in [([1,0],[3,0],'CONTACT'),([-1,1],[1,-1],'CONTACT'),
                           ([-1,3],[3,3],'DISJOINT'),([1,1],[1,1],'DISJOINT'),
                           ([0,1],[0,1],'CONTACT')]:
            proof=compile_boundary_contact_certificate(SQUARE,a,b)
            self.assertEqual(proof['status'],status)
            self.assertFalse(proof['kernel_checked'])

    def test_cli_geometric_proof(self):
        from perfectpower.belyaev_cli import dispatch
        result=dispatch('geometric-route-proof',{'obstacles':[SQUARE],'start':[-1,1],'end':[3,1]})
        self.assertEqual(result['proof']['schema'],'pp-lean-geometric-route/1')

if __name__=='__main__':unittest.main()
