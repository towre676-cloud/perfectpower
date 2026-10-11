from fractions import Fraction as Q
from hashlib import sha256
import copy,json,random,unittest
from pathlib import Path
from perfectpower import planar_certificates as p
from perfectpower.divisor_square import Budget,WorkLimit
from perfectpower.belyaev_geometry import triangulate,locate_point
from perfectpower.polygon_routing import route,segment_visibility
from perfectpower.geometry_certificates import certify_route
from perfectpower.belyaev_cli import dispatch
SQUARE=[[0,0],[2,0],[2,2],[0,2]]
TRIS=[[[0,0],[2,0],[2,2]],[[0,0],[2,2],[0,2]]]
CONCAVE=[[0,0],[4,0],[4,1],[1,1],[1,4],[0,4]]
def at(f,point):
    def sign(a):
        v=a[0]*point[0]+a[1]*point[1]+a[2]
        return -1 if v<0 else 0 if v==0 else 1
    return p.evaluate(f,{a:sign(a) for a in p.leaves(f)})
class PlanarCertificates(unittest.TestCase):
    def test_farkas_strict_and_nonstrict(self):
        for cs in ([((Q(1),Q(0),Q(0)),True),((Q(-1),Q(0),Q(0)),False)],
                   [((Q(0),Q(0),Q(-1)),False)]):
            w=p.contradiction(cs,Budget(1000));self.assertIsNotNone(w)
            total=tuple(sum(wi*a[j] for wi,(a,_) in zip(w,cs)) for j in range(3))
            self.assertTrue(all(wi>=0 for wi in w));self.assertEqual(total[:2],(0,0))
            self.assertTrue(total[2]<0 or total[2]==0 and any(wi>0 and strict for wi,(_,strict) in zip(w,cs)))
        self.assertIsNone(p.contradiction([((Q(0),Q(0),Q(0)),False)],Budget(100)))
    def test_false_identity_rejected(self):
        with self.assertRaisesRegex(ValueError,'counterexample'):p.prove(p.eq((Q(1),Q(0),Q(0))))
    def test_budget_not_acceptance(self):
        with self.assertRaises(WorkLimit):p.prove(p.filled(list(map(p.point,SQUARE))),work_limit=1)
        with self.assertRaises(WorkLimit):p.prove(p.filled(list(map(p.point,SQUARE))),atom_limit=1)
    def test_concave_real_formula_at_exact_points(self):
        f=p.filled(list(map(p.point,CONCAVE)));rng=random.Random(123)
        for _ in range(120):
            point=(Q(rng.randrange(-2,11),2),Q(rng.randrange(-2,11),2))
            self.assertEqual(at(f,point),locate_point(CONCAVE,point)!='OUTSIDE')
        self.assertFalse(at(f,(Q(2),Q(2))))
    def test_steiner_and_source_bound_hash(self):
        fans=[[SQUARE[i],SQUARE[(i+1)%4],[1,1]] for i in range(4)]
        r,s=p.compile_mesh_coverage(SQUARE,fans)
        self.assertEqual(r['proof']['source_sha256'],sha256(s.encode()).hexdigest())
        self.assertFalse(r['proof']['kernel_checked']);self.assertIn('∀ p : Point',s)
        self.assertIn('checked_split',s)
    def test_missing_and_external_triangle_rejected(self):
        for ts in ([TRIS[0]],TRIS+[[[5,5],[6,5],[5,6]]]):
            with self.assertRaises(ValueError):p.compile_mesh_coverage(SQUARE,ts)
    def test_concave_triangulation_formula(self):
        tris=triangulate(CONCAVE)['triangles'];f=p.same(p.filled(list(map(p.point,CONCAVE))),p.any_([p.triangle(list(map(p.point,t))) for t in tris]))
        for x in range(-1,6):
            for y in range(-1,6):self.assertTrue(at(f,(Q(x),Q(y))))
    def test_tangent_overlap_and_boundary(self):
        for polygons,a,b in [([SQUARE],[-1,0],[3,0]),([SQUARE],[-1,1],[1,-1]),([SQUARE,SQUARE],[-1,0],[3,0])]:
            r,s=p.compile_real_segment(polygons,a,b)
            self.assertEqual(r['evidence']['status'],'FREE');self.assertIn('real_free',s)
            self.assertTrue(segment_visibility(polygons,a,b)['visible'])
    def test_crossing_is_actual_blocked_parameter(self):
        r,s=p.compile_real_segment([SQUARE],[-1,1],[3,1]);t=Q(r['evidence']['parameter'])
        self.assertGreater(t,0);self.assertLess(t,1);self.assertIn('blocked_segment',s)
        self.assertEqual(r['evidence']['status'],'BLOCKED')
    def test_zero_segment(self):
        for a,status in [([0,0],'FREE'),([1,1],'BLOCKED'),([3,3],'FREE')]:
            r,_=p.compile_real_segment([SQUARE],a,a);self.assertEqual(r['evidence']['status'],status)
    def test_route_original_rational_units(self):
        packet=route([],['1/3','2/7'],['4/3','9/7'])
        r,s=p.compile_real_route(packet,certify_route(packet))
        self.assertIn('no_cheaper_real_walk',s);self.assertIn('real_complete',s)
        self.assertEqual(len(r['pair_evidence']),3)
        self.assertIn('real_source_free',s);self.assertIn('retained_real_walk',s)
    def test_zero_route_has_independent_point_admission(self):
        packet=route([SQUARE],[0,0],[0,0]);r,s=p.compile_real_route(packet,certify_route(packet))
        self.assertEqual(r['pair_evidence']['source_stationary']['status'],'FREE')
        self.assertIn('real_source_free',s);self.assertIn('retained_real_walk',s)
        with self.assertRaises(ValueError):route([SQUARE],[1,1],[1,1])
    def test_malformed_graph_rejected(self):
        original=route([SQUARE],[0,0],[2,2]);dual=certify_route(original)
        for mutate in ('missing','invented','weight'):
            packet=copy.deepcopy(original)
            if mutate=='missing':packet['edges']=packet['edges'][1:]
            elif mutate=='invented':packet['edges'].append([0,1,'4'])
            else:packet['edges'][0][2]='100'
            with self.assertRaises(ValueError):p.compile_real_route(packet,dual)
    def test_disconnected_regions_retain_no_route(self):
        ring=[[[-3,1],[3,1],[3,3],[-3,3]],[[-3,-3],[3,-3],[3,-1],[-3,-1]],
              [[-3,-3],[-1,-3],[-1,3],[-3,3]],[[1,-3],[3,-3],[3,3],[1,3]]]
        packet=route(ring,[0,0],[5,0]);self.assertEqual(packet['status'],'UNREACHABLE')
        self.assertNotIn(packet['vertices'].index(packet['end']),certify_route(packet)['reachable'])
    def test_cli_real_segment(self):
        r=dispatch('real-segment-proof',{'obstacles':[],'start':[0,0],'end':[1,1]})
        self.assertEqual(r['certificate']['schema'],'pp-real-segment/1')
    def test_namespace_injection_rejected(self):
        for compiler,args in [(p.compile_real_segment,([], [0,0],[1,1])),(p.compile_mesh_coverage,(SQUARE,TRIS))]:
            with self.assertRaises(ValueError):compiler(*args,namespace='X; axiom bad : False')
    def test_real_contact_and_disjoint(self):
        for args,exists in [(([0,0],[2,2],[0,2],[2,0]),True),(([0,0],[3,0],[1,0],[4,0]),True),
                            (([0,0],[0,0],[0,0],[1,1]),True),(([0,0],[1,0],[2,0],[3,0]),False)]:
            r,s=p.compile_real_contact(*args)
            self.assertEqual(bool(r['producer_intersection']['points']),exists)
            self.assertIn('source_contact' if exists else 'source_disjoint',s)
            self.assertFalse(r['proof']['kernel_checked'])
    def test_actual_contact_formula(self):
        a,b,c,d=map(p.point,([0,0],[2,2],[0,2],[2,0]))
        f=p.and_(p.boundary(a,b),p.boundary(c,d))
        self.assertTrue(at(f,(Q(1),Q(1))))
        self.assertFalse(at(f,(Q(0),Q(0))))
    def test_retained_exact_source_hashes(self):
        root=Path(__file__).resolve().parents[2]
        for source in (root/'receipts/planar_closure').glob('*.lean'):
            meta=json.loads(source.with_suffix('.json').read_text())
            self.assertEqual(meta['proof']['source_sha256'],sha256(source.read_bytes()).hexdigest())
if __name__=='__main__':unittest.main()
