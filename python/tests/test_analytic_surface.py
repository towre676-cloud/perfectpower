import unittest,math,random,importlib.util
from fractions import Fraction as Q
from perfectpower.intrinsic_torus import legendre_torus,voronoi,distance,legendre_point

class IntrinsicTorusTests(unittest.TestCase):
    def test_area_and_quotient_topology(self):
        for lam in ('1/10','1/3','1/2','2/3','9/10'):
            p=legendre_torus(lam);t=p['topology_diagnostics']
            self.assertAlmostEqual(p['total_cell_area'],p['height'],places=12)
            self.assertEqual(t['euler'],0);self.assertEqual(t['face_charge'],0)
            self.assertTrue(t['trivalent']);self.assertTrue(t['two_face_edge_incidence']);self.assertTrue(t['disk_cell_condition'])
    def test_cells_use_continuous_periodic_distances(self):
        p=legendre_torus('1/3');h=p['height'];sites=p['sites']
        for cell in p['cells']:
            index=cell['site'];poly=cell['lifted_polygon']
            probes=poly+[[sum(a[k] for a in poly)/len(poly) for k in range(2)]]
            for q in probes:
                own=distance(q,sites[index],h)
                self.assertLessEqual(own,min(distance(q,s,h) for s in sites)+1e-9)
    def test_translation_and_periodic_site_equivalence(self):
        p=legendre_torus('1/2');sites=p['sites'];h=p['height']
        q=voronoi(h,[[s[0]+2.17,s[1]-3*h+.29] for s in sites])
        for a,b in zip(p['cells'],q['cells']):self.assertAlmostEqual(a['area'],b['area'],places=11)
    def test_actual_curve_points(self):
        for lam in ('1/10','1/2','9/10'):
            p=legendre_torus(lam)
            for s in p['sites']:
                point=legendre_point(Q(lam),complex(*s),p['height'])
                self.assertLess(point['relative_equation_residual'],1e-10)
    def test_domain_and_degeneracy(self):
        with self.assertRaises(ValueError):voronoi(1,[[0,0],[1,0]])
        with self.assertRaises(ValueError):voronoi(0,[[0,0]])
        with self.assertRaises(ValueError):legendre_torus('1/10',terms=4)
        self.assertFalse(voronoi(1,[[.2,.3]])['topology_diagnostics']['disk_cell_condition'])

@unittest.skipUnless(importlib.util.find_spec('scipy') and importlib.util.find_spec('numpy'),'optional numerical backend unavailable')
class AnalyticSurfaceTests(unittest.TestCase):
    def setUp(self):
        from perfectpower.analytic_surface import AnalyticSurface
        self.s=AnalyticSurface([0,4,0,-5,0,1],2)
    def test_metric_and_curvature_formula(self):
        for x in (.3+.7j,3+2j,-.4+1.1j):
            p=self.s.metric(x);rho=p['density_in_x_chart']
            # Genus two: rho=(1+|x|^2)/|R(x)| and K=-2/[rho*(1+|x|^2)^2].
            self.assertAlmostEqual(p['curvature'],-2/(rho*(1+abs(x)**2)**2),places=10)
    def test_smooth_branch_and_infinity_charts(self):
        for i in range(len(self.s.roots)):self.assertGreater(self.s.branch_metric(i)['density_at_t_zero'],0)
        self.assertEqual(self.s.infinity_metric()['density_at_t_zero'],4)
    def test_period_against_independent_real_cut_integral(self):
        from scipy.integrate import quad
        p=self.s.circle_period(-1.5,.6)
        def x(t):return -2+math.sin(t)**2
        def unit(t):return math.sqrt(abs(x(t)*(x(t)-1)*(x(t)-2)))
        expected0=4*quad(lambda t:1/unit(t),0,math.pi/2,epsabs=1e-12)[0]
        expected1=4*quad(lambda t:x(t)/unit(t),0,math.pi/2,epsabs=1e-12)[0]
        self.assertAlmostEqual(abs(p['period_vector'][0][0]),expected0,places=10)
        self.assertAlmostEqual(abs(p['period_vector'][1][0]),abs(expected1),places=10)
        self.assertLess(abs(p['period_vector'][0][1]),1e-10)
    def test_contour_deformation_and_contractible_loop(self):
        a=self.s.circle_period(-1.5,.6);b=self.s.circle_period(-1.5,.7)
        for v,w in zip(a['period_vector'],b['period_vector']):self.assertLess(math.dist(v,w),1e-9)
        p=self.s.circle_period(-2,.15)
        self.assertEqual(p['turns_to_close_lift'],2)
        self.assertLess(max(math.hypot(*v) for v in p['period_vector']),1e-9)
    def test_commutator_continuation_and_inverse(self):
        from perfectpower.analytic_surface import AnalyticSurface
        s=AnalyticSurface([-1,0,0,1],3)
        p=s.word_period([1,2,-1,-2]);q=s.word_period([2,1,-2,-1])
        self.assertGreater(math.hypot(*p['period_vector'][0]),1)
        for a,b in zip(p['period_vector'],q['period_vector']):self.assertLess(math.hypot(a[0]+b[0],a[1]+b[1]),1e-8)
        z=s.word_period([1,-1]);self.assertLess(math.hypot(*z['period_vector'][0]),1e-8)
        with self.assertRaises(ValueError):s.word_period([1])
    def test_zero_genus_and_root_collision_rejection(self):
        from perfectpower.analytic_surface import AnalyticSurface
        with self.assertRaises(ValueError):AnalyticSurface([1,0,1],2).metric(.5j)
        with self.assertRaises(ValueError):self.s.circle_period(-1.5,.5)

@unittest.skipUnless(importlib.util.find_spec('scipy') and importlib.util.find_spec('numpy'),'optional numerical backend unavailable')
class ConformalMeshTests(unittest.TestCase):
    def test_original_genus_two_and_intrinsic_cells(self):
        from perfectpower.conformal_mesh import hyperelliptic_mesh,heat_voronoi
        p=hyperelliptic_mesh([0,-1,0,0,0,1],4);v=heat_voronoi(p,6)
        self.assertEqual(p['genus'],2);self.assertEqual(p['euler'],-2)
        self.assertTrue(p['closed_manifold_vertex_links']);self.assertTrue(p['orientable']);self.assertTrue(p['connected'])
        self.assertLess(abs(p['total_defect']+4*math.pi),1e-10)
        self.assertLess(abs(v['area_partition_residual']),1e-10)
        self.assertTrue(all(a>0 for a in v['cell_areas']))
        self.assertEqual(len(set(v['sites'])),6)
        for piece in v['pieces']:
            for bary in piece['barycentric_polygon']:
                self.assertAlmostEqual(sum(bary),1,places=10)
                self.assertGreaterEqual(min(bary),-1e-10)
    def test_even_degree_infinity_and_genus_three(self):
        from perfectpower.conformal_mesh import hyperelliptic_mesh
        for coeff,g in (([-1,0,0,0,1],1),([-1,0,0,0,0,0,0,1],3)):
            p=hyperelliptic_mesh(coeff,6)
            self.assertEqual(p['euler'],2-2*g)
            self.assertLess(abs(p['gauss_bonnet_residual']),1e-9)
