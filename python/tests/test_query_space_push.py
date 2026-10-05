import unittest,json
from copy import deepcopy
from perfectpower.coefficient_charts import *
from perfectpower.polynomial_charts import parameterize_relation,evaluate_parameterization,verify_parameterization
from perfectpower.curve_queries import query_curve,verify_curve_query
from perfectpower.integer_image_index import IntegerImageIndex
from perfectpower.recurrence_domains import *
from perfectpower.core import integer_power_root

class QuerySpacePush(unittest.TestCase):
    def test_compiled_space_isolated(self):
        from perfectpower.query_space import CurveSpace
        space=CurveSpace([0,0,2],[0,0,0,3])
        g=space.generator;g['charts'].clear()
        first=space.query({'expr':'y','relation':'>'},objective='x*x+y*y')
        second=space.query({'expr':'y-600','relation':'<='},point_limit=0)
        self.assertEqual(first['optimization']['optimizer_count'],2)
        self.assertEqual(second['solution_count'],21)
        self.assertEqual(space.statistics()['compilations'],1)
        self.assertEqual(space.statistics()['queries'],2)
        self.assertTrue(verify_curve_query(first));self.assertTrue(verify_curve_query(second))

    def test_automatic_smt_projection_and_model(self):
        from perfectpower.simplifier import simplify_query,verify_simplification,lift_model
        script='(set-logic QF_NIA)(declare-const x Int)(declare-const y Int)(assert (= (* 2 x x) (* 3 y y y)))(assert (< x 0))(assert (> y 0))(assert (<= y 600))(check-sat)'
        result=simplify_query(script)
        self.assertEqual(result['steps'][0]['method'],'polynomial_charts')
        self.assertIn('(set-logic QF_LIA)',result['residual'])
        self.assertTrue(verify_simplification(result))
        self.assertEqual(lift_model(result,{'_pp_curve':2}),{'x':-144,'y':24})
        with self.assertRaises(ValueError):lift_model(result,{'_pp_curve':11})

    def test_primitive_square_cube(self):
        r=primitive_power_charts(2,2,3,3)
        self.assertEqual((r['left_scale'],r['right_scale']),(18,6))
        self.assertEqual(primitive_points(r,2),[(-144,24),(144,24)])
        self.assertTrue(verify_primitive_charts(r))

    def test_bounded_independent_chart_completeness(self):
        for c,d,p,q in [(2,3,2,3),(3,2,3,2),(-2,3,3,2),(2,1,2,4),
                        (4,9,2,2),(-4,-9,4,4),(8,2,4,6),(6,10,3,3),
                        (1,-1,2,2),(16,81,4,4),(2,-3,3,3)]:
            r=primitive_power_charts(c,p,d,q)
            actual={(x,y) for x in range(-60,61) for y in range(-60,61) if c*x**p==d*y**q}
            generated={pt for t in range(61) for pt in primitive_points(r,t) if all(abs(v)<=60 for v in pt)}
            self.assertEqual(actual,generated,(c,d,p,q))

    def test_obstructed_zero(self):
        r=primitive_power_charts(2,2,1,4)
        self.assertEqual(r['obstruction']['prime'],2)
        self.assertEqual(primitive_points(r,0),[(0,0)])
        self.assertEqual(primitive_points(r,1),[])
        self.assertEqual(primitive_power_charts(1,2,-1,2)['signs'],[])

    def test_primitive_tamper(self):
        r=primitive_power_charts(2,2,3,3);r['left_scale']=1
        self.assertFalse(verify_primitive_charts(r))

    def test_expanded_affine(self):
        # 2*(2x+2)^2+7 = 3*(3y-3)^3+7
        left=[15,16,8];right=[-74,243,-243,81]
        r=parameterize_relation(left,right)
        self.assertTrue(verify_parameterization(json.loads(json.dumps(r))))
        actual={(x,y) for x in range(-40,41) for y in range(-40,41)
                if 2*(2*x+2)**2==3*(3*y-3)**3}
        generated={pt for t in range(41) for pt in evaluate_parameterization(r,t)['points'] if all(abs(v)<=40 for v in pt)}
        self.assertEqual(actual,generated)

    def test_huge_curve_count_and_ties(self):
        T=10**40
        r=query_curve([0,0,2],[0,0,0,3],{'expr':'y-'+str(6*T*T),'relation':'<='},point_limit=0)
        self.assertEqual(r['solution_count'],2*T+1)
        self.assertTrue(verify_curve_query(r))
        r=query_curve([0,0,2],[0,0,0,3],{'expr':'y','relation':'>'},objective='x*x+y*y')
        self.assertEqual(r['optimization']['value'],'360')
        self.assertEqual(r['optimization']['optimizer_points'],[(-18,6),(18,6)])
        self.assertTrue(verify_curve_query(r))

    def test_empty_affine_image(self):
        # 2*(2x+1)^2 = y^4 has only zero magnitudes, which the x image excludes.
        r=query_curve([2,8,8],[0,0,0,0,1])
        self.assertEqual(r['solution_count'],0)
        self.assertTrue(verify_curve_query(r))

    def test_fibre_cache_isolated(self):
        index=IntegerImageIndex(capacity=2)
        a=index.fibre([-1,0,1]);a['roots'].clear()
        self.assertEqual(index.points([0,0,1],1),[-1,1])
        self.assertEqual(index.statistics()['hits'],1)
        with self.assertRaises(WorkLimit):index.fibre([-1,0,1],node_limit=1)

    def test_nonlinear_cache_shared(self):
        index=IntegerImageIndex()
        r=parameterize_relation([2,4,6,4,2],[0,0,0,3])
        a=evaluate_parameterization(r,1,image_index=index)
        b=evaluate_parameterization(r,1,image_index=index)
        self.assertEqual(a,b);self.assertGreater(index.hits,0)

    def test_orbit_phase_and_large_queries(self):
        o=recurrence_orbit([3,0,1],[1,1,1],8,1)
        self.assertEqual((o['cycle_start'],o['period']),(4,8))
        self.assertTrue(verify_orbit(o))
        value=1
        for n in range(300):
            self.assertEqual(orbit_value(o,n),value)
            value=((n*n+3)*value*pow(n*n+n+1,-1,8))%8
        d=orbit_domain(o,power=2)
        self.assertTrue(verify_orbit_domain(d))
        self.assertEqual(orbit_count(d,0,10**100),10**100)
        self.assertEqual(orbit_select(d,10**100),10**100+1)

    def test_recurrence_global_optimum(self):
        d=orbit_domain(recurrence_orbit([2],[1],7,1),residues=[1,2])
        # Hit indices are 0 or 1 modulo 3; phase 2 has two nearest neighbors.
        H=3*10**30+2
        r=orbit_optimize(d,[H*H,-2*H,1])
        self.assertEqual(r['value'],1)
        self.assertEqual(r['points'],[H-1,H+1])
        self.assertTrue(verify_orbit_optimum(r))
        r=orbit_optimize(d,[1,-1]);self.assertEqual(r['status'],'UNBOUNDED')
        empty=orbit_domain(recurrence_orbit([1],[1],7,1),residues=[3])
        self.assertEqual(orbit_optimize(empty,[0,0,1])['status'],'EMPTY')

    def test_singular_prefix(self):
        o=recurrence_orbit([1],[1,1],6,1)
        self.assertEqual(o['singular_index'],1)
        self.assertEqual(o['next_values']['count'],0)
        d=orbit_domain(o,power=2)
        self.assertFalse(d['complete']);self.assertEqual(orbit_count(d,0,1),2)
        with self.assertRaises(ValueError):orbit_count(d,0,2)
        with self.assertRaises(ValueError):orbit_select(d,1)
        with self.assertRaises(ValueError):orbit_value(o,2)

    def test_singular_cosets(self):
        for m in range(2,20):
            for q in range(m):
                for rhs in range(m):
                    r=next_congruence(q,rhs,m)
                    actual=[v for v in range(m) if q*v%m==rhs]
                    expected=[] if not r['count'] else [r['base']+i*r['step'] for i in range(r['count'])]
                    self.assertEqual(actual,expected)

    def test_transient_and_empty_hits(self):
        o=recurrence_orbit([2],[1],8,1)
        self.assertEqual(o['cycle_start'],3)
        self.assertEqual(orbit_value(o,10**100),0)
        d=orbit_domain(o,residues=[3]);self.assertEqual(orbit_count(d,0,10**100),0)
        self.assertIsNone(orbit_select(d,0))

    def test_budget_and_domains(self):
        with self.assertRaises(WorkLimit):factor_integer(1000003*1000033,work_limit=10)
        with self.assertRaises(WorkLimit):recurrence_orbit([1],[1],101,1,step_limit=2)
        with self.assertRaises(ValueError):primitive_power_charts(0,2,1,3)
        with self.assertRaises(ValueError):recurrence_orbit([1],[1],1,1)
        with self.assertRaises(ValueError):primitive_points(primitive_power_charts(1,2,1,3),-1)

    def test_orbit_tamper(self):
        o=recurrence_orbit([1,1],[1],7,1);o['states'][0][1]=2
        self.assertFalse(verify_orbit(o))
        d=orbit_domain(recurrence_orbit([1],[1],7,1),power=2);d['cells'][0]['residues']=[]
        self.assertFalse(verify_orbit_domain(d))

if __name__=='__main__':unittest.main()
