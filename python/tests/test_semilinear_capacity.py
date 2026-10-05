import copy
import json
import random
import unittest
from fractions import Fraction as Q
from perfectpower import polyalg as P
from perfectpower.residue_cover import evaluate
from perfectpower.semilinear_domains import (semilinear_domain,verify_domain,contains,count_domain,
    select,optimize_semilinear,verify_optimization,project_semilinear_query)
from perfectpower.polynomial_charts import (parameterize_relation,verify_parameterization,
    evaluate_parameterization)
from perfectpower.curve_queries import query_curve,verify_curve_query
from perfectpower.polynomial_relations import solve_relation,verify_relation
from perfectpower.gamma_polynomial import gamma_domain,optimize_gamma,verify_gamma_domain,verify_gamma_optimum
from perfectpower.simplifier import simplify_query,lift_model,verify_simplification,_eval
from perfectpower.integer_projection import _parse_integer_query
from perfectpower.divisor_square import WorkLimit


def sign(f,op):return {'poly':f,'relation':op}
def mod(f,m,op,v):return {'poly':f,'modulus':m,'relation':op,'value':v}
def conj(*args):return {'op':'and','args':list(args)}
def curve(expr,op):return {'expr':expr,'relation':op}
def box(b):return conj(curve(f'x+{b}','>='),curve(f'x-{b}','<='),curve(f'y+{b}','>='),curve(f'y-{b}','<='))


def independent_truth(predicate,n):
    if type(predicate) is bool:return predicate
    if 'poly' in predicate:
        value=sum(c*n**i for i,c in enumerate(predicate['poly']))
        target=0
        if 'modulus' in predicate:value%=predicate['modulus'];target=predicate['value']
        return {'=':value==target,'!=':value!=target,'<':value<target,'<=':value<=target,'>':value>target,'>=':value>=target}[predicate['relation']]
    values=[independent_truth(p,n) for p in predicate['args']]
    return all(values) if predicate['op']=='and' else any(values) if predicate['op']=='or' else not values[0]


def powered(a,b,p,k=0):
    f=list(map(int,P.power(P.poly([b,a]),p)));f[0]+=k;return f


def smt(names,atoms):
    return '(set-logic QF_NIA)'+''.join(f'(declare-const {n} Int)' for n in names)+''.join(f'(assert {a})' for a in atoms)+'(check-sat)'


class SemilinearTests(unittest.TestCase):
    def test_random_boolean_domains_counts_and_selection(self):
        rng=random.Random(502711)
        for _ in range(100):
            a=sign([rng.randint(-9,9),rng.randint(-5,5),rng.choice((-2,-1,1,2))],rng.choice(('<=','>','!=')))
            b=mod([rng.randint(-6,6),rng.randint(-5,5),1],rng.randint(2,7),rng.choice(('=','!=','<')),rng.randint(-1,7))
            c=mod([0,1],rng.randint(2,7),'=',rng.randint(0,3))
            predicate={'op':'or','args':[conj(a,b),{'op':'not','args':[c]}]}
            d=semilinear_domain(predicate)
            self.assertTrue(verify_domain(json.loads(json.dumps(d))))
            for n in range(-70,71):self.assertEqual(contains(d,n),independent_truth(predicate,n))
            expected=[n for n in range(-35,36) if independent_truth(predicate,n)]
            self.assertEqual(count_domain(d,-35,35),len(expected))
            for i in (0,len(expected)//2,len(expected)-1):
                if expected:self.assertEqual(select(d,i,start=-35),expected[i])

    def test_period_compression_and_outside_modular_threshold(self):
        d=semilinear_domain(mod([0,-1,1],2,'=',0))
        self.assertEqual(d['cells'],[{'interval':[None,None],'modulus':1,'residues':[0]}])
        self.assertEqual(d['nonnegative_density'],'1');self.assertTrue(verify_domain(d))
        d=semilinear_domain(mod([0,1],7,'!=',-1));self.assertEqual(d['period'],7)
        self.assertEqual(d['cells'][0]['modulus'],1)

    def test_empty_bounded_residue_cell(self):
        p=conj(sign([0,1],'='),mod([0,1],3,'=',1));d=semilinear_domain(p)
        self.assertEqual(d['cardinality'],0);self.assertEqual(d['cells'],[])
        self.assertIsNone(select(d,0));self.assertEqual(optimize_semilinear(p,[4])['status'],'EMPTY')

    def test_huge_rank_count_and_density(self):
        d=semilinear_domain(conj(sign([0,1],'>='),mod([0,1],7,'=',3)))
        h=10**100;self.assertEqual(select(d,h),7*h+3)
        self.assertEqual(count_domain(d,0,7*h+3),h+1);self.assertEqual(d['nonnegative_density'],'1/7')
        self.assertTrue(verify_domain(d))

    def test_negative_endpoints_and_finite_selection(self):
        d=semilinear_domain(conj(sign([20,1],'>='),sign([-4,1],'<='),mod([0,1],5,'=',2)))
        expected=[n for n in range(-20,5) if n%5==2]
        self.assertEqual(d['cardinality'],len(expected));self.assertEqual([select(d,i,start=-20) for i in range(len(expected))],expected)
        self.assertIsNone(select(d,len(expected),start=-20));self.assertIsNone(select(d,0,start=5))

    def test_domain_tampering_and_work_limits(self):
        d=semilinear_domain(mod([0,1],7,'=',3));bad=copy.deepcopy(d);bad['cells'][0]['residues']=[4]
        self.assertFalse(verify_domain(bad));bad=copy.deepcopy(d);bad['nonnegative_density']='1';self.assertFalse(verify_domain(bad))
        with self.assertRaises(WorkLimit):semilinear_domain(mod([0,1],1009,'=',0),period_limit=100)
        with self.assertRaises(WorkLimit):semilinear_domain(mod([0,1],97,'=',0),work_limit=1)
        with self.assertRaises(ValueError):semilinear_domain(mod([0,1],0,'=',0))

    def test_random_bounded_optimization_all_ties(self):
        rng=random.Random(104552)
        for i in range(100):
            p=conj(sign([25,1],'>='),sign([-25,1],'<='),
                   {'op':'or','args':[mod([1,0,1],rng.randint(2,8),'=',rng.randint(0,7)),mod([0,1],rng.randint(2,8),'=',rng.randint(0,7))]})
            f=[rng.randint(-8,8) for _ in range(4)]+[rng.choice((-2,-1,1,2))]
            values=[(n,sum(c*n**j for j,c in enumerate(f))) for n in range(-25,26) if independent_truth(p,n)]
            sense='min' if i%2 else 'max';r=optimize_semilinear(p,f,sense=sense)
            self.assertTrue(verify_optimization(json.loads(json.dumps(r))))
            if not values:self.assertEqual(r['status'],'EMPTY');continue
            value=(min if sense=='min' else max)(v for n,v in values)
            self.assertEqual(r['value'],value);self.assertEqual(r['points'],[n for n,v in values if v==value])

    def test_sparse_lattice_huge_ties(self):
        h=10**60;p={'op':'or','args':[mod([0,1],1000,'=',(h-300)%1000),mod([0,1],1000,'=',(h+300)%1000)]}
        r=optimize_semilinear(p,[h*h,-2*h,1])
        self.assertEqual((r['value'],r['points']),(90000,[h-300,h+300]));self.assertTrue(verify_optimization(r))
        self.assertLess(r['root_nodes'],1000)

    def test_different_cell_periods_and_constants(self):
        p={'op':'or','args':[conj(sign([0,1],'<='),mod([0,1],2,'=',0)),conj(sign([0,1],'>'),mod([0,1],3,'=',1))]}
        r=optimize_semilinear(p,[1,-2,1]);self.assertEqual(r['points'],[1]);self.assertTrue(verify_optimization(r))
        c=optimize_semilinear(p,[7]);self.assertIsNone(c['points']);self.assertIsNone(c['optimizer_domain']['cardinality']);self.assertTrue(verify_optimization(c))
        self.assertEqual(optimize_semilinear(p,[0,1])['status'],'UNBOUNDED')

    def test_optimum_tampering_and_shared_budget(self):
        p=mod([0,1],13,'=',3);r=optimize_semilinear(p,[0,0,1])
        r['points'].append(16);self.assertFalse(verify_optimization(r))
        with self.assertRaises(WorkLimit):optimize_semilinear(p,[0,0,1],node_limit=1)

    def test_pointwise_smt_modular_projection(self):
        s=smt('x',['(<= (* x x) 100)','(= (mod (+ (* x x) x) 5) 2)'])
        r=project_semilinear_query(s);names,before=_parse_integer_query(s);_,after=_parse_integer_query(r['smt'].replace('QF_LIA','QF_NIA',1))
        for n in range(-30,31):self.assertEqual(all(_eval(a,{'x':n}) for a in before),all(_eval(a,{'x':n}) for a in after))
        reduction=simplify_query(s);self.assertIn('semilinear_domain',[a['method'] for a in reduction['steps']]);self.assertTrue(verify_simplification(reduction))

    def test_unsupported_variable_modulus_keeps_residual(self):
        with self.assertRaises(ValueError):project_semilinear_query(smt('x',['(= (mod x x) 1)']))
        with self.assertRaises(WorkLimit):project_semilinear_query(smt('x',['(= (mod x 1009) 1)']),period_limit=20)


class CurveChartTests(unittest.TestCase):
    def test_four_signs_and_unique_zero(self):
        c=parameterize_relation([0,0,0,0,1],[0,0,0,0,0,0,1]);self.assertTrue(verify_parameterization(c))
        self.assertEqual(len(c['charts']),4);self.assertEqual(evaluate_parameterization(c,0)['points'],[(0,0)])
        self.assertEqual(evaluate_parameterization(c,2)['points'],[(-8,-4),(-8,4),(8,-4),(8,4)])

    def test_affine_images_can_prove_global_emptiness(self):
        c=parameterize_relation(powered(2,1,2),powered(2,0,3));self.assertEqual(c['status'],'COMPLETE');self.assertEqual(c['points'],[])
        self.assertTrue(verify_parameterization(c));r=solve_relation(powered(2,1,2),powered(2,0,3))
        self.assertEqual(r['points'],[]);self.assertTrue(verify_relation(r))

    def test_shifted_negative_affine_coordinates(self):
        c=parameterize_relation(powered(-3,2,3,7),powered(5,-1,4,7));self.assertTrue(verify_parameterization(c))
        for t in range(20):
            for x,y in evaluate_parameterization(c,t)['points']:self.assertEqual((-3*x+2)**3+7,(5*y-1)**4+7)

    def test_common_outer_retains_off_diagonal(self):
        r=query_curve([0,0,1],[0,0,1],curve('x-y','!='))
        self.assertIsNone(r['solution_count']);self.assertTrue(verify_curve_query(r))
        q=query_curve([0,0,1],[0,0,1],conj(box(5),curve('x-y','!=')))
        self.assertEqual(q['points'],[(n,-n) for n in range(-5,6) if n]);self.assertEqual(q['solution_count'],10)

    def test_nonlinear_fibres_every_preimage_and_zero(self):
        f=[1,0,-2,0,1];c=parameterize_relation(f,f);self.assertTrue(verify_parameterization(c))
        self.assertEqual(evaluate_parameterization(c,0)['points'],[(-1,-1),(-1,1),(1,-1),(1,1)])
        points={p for t in range(9) for p in evaluate_parameterization(c,t)['points'] if all(abs(n)<=3 for n in p)}
        expected={(x,y) for x in range(-3,4) for y in range(-3,4) if (x*x-1)**2==(y*y-1)**2}
        self.assertEqual(points,expected);self.assertEqual(query_curve(f,f)['status'],'UNRESOLVED')

    def test_chart_tampering_and_nonpower_unknown(self):
        c=parameterize_relation([0,0,1],[0,0,0,1]);c['charts'][0]['x']['numerator'][0]=1
        self.assertFalse(verify_parameterization(c));self.assertEqual(parameterize_relation([1,1,1],[0,0,0,1])['status'],'UNRESOLVED')

    def test_random_boxes_independent_points_and_bivariate_optimization(self):
        rng=random.Random(919941)
        for i in range(60):
            a,b,c,d=rng.choice((-3,-2,1,2,3)),rng.randint(-4,4),rng.choice((-3,-2,1,2,3)),rng.randint(-4,4)
            p,q=rng.randint(2,6),rng.randint(2,6);k=rng.randint(-5,5)
            left,right=powered(a,b,p,k),powered(c,d,q,k)
            predicate=conj(box(15),{'expr':'x','modulus':5,'relation':'!=','value':2})
            r=query_curve(left,right,predicate,objective='x*x+2*x*y+2*y*y-5*x+3*y',point_limit=2000,sense='min' if i%2 else 'max')
            expected=[(x,y) for x in range(-15,16) for y in range(-15,16) if (a*x+b)**p==(c*y+d)**q and x%5!=2]
            self.assertTrue(verify_curve_query(json.loads(json.dumps(r))));self.assertEqual(r['points'],expected);self.assertEqual(r['solution_count'],len(expected))
            if not expected:self.assertEqual(r['optimization']['status'],'EMPTY');continue
            values=[(x*x+2*x*y+2*y*y-5*x+3*y,(x,y)) for x,y in expected]
            value=(min if i%2 else max)(v for v,p in values)
            self.assertEqual(r['optimization']['value'],str(value));self.assertEqual(r['optimization']['optimizer_points'],[p for v,p in values if v==value])

    def test_huge_curve_count_without_box_scan(self):
        h=10**90;p=conj(curve('x','>='),curve('y','>='),curve(f'x-{h}','<='),curve(f'y-{h}','<='))
        r=query_curve([0,0,1],[0,0,0,1],p)
        self.assertEqual(r['solution_count'],10**30+1);self.assertIsNone(r['points']);self.assertTrue(verify_curve_query(r))

    def test_huge_curve_objective_keeps_both_original_points(self):
        h=10**30;r=query_curve([0,0,1],[0,0,0,1],objective=f'(y-{h*h})**2')
        self.assertEqual(r['optimization']['value'],'0');self.assertEqual(r['optimization']['optimizer_points'],[(-h**3,h*h),(h**3,h*h)])
        self.assertTrue(verify_curve_query(r));self.assertLess(r['root_nodes'],10000)

    def test_constant_curve_objective_and_unbounded(self):
        r=query_curve([0,0,1],[0,0,0,1],objective='7');self.assertEqual(r['optimization']['value'],'7')
        self.assertIsNone(r['optimization']['optimizer_count']);self.assertTrue(verify_curve_query(r))
        self.assertEqual(query_curve([0,0,1],[0,0,0,1],objective='x')['optimization']['status'],'UNBOUNDED')

    def test_coordinate_modulo_denominator_clearing(self):
        r=query_curve(powered(3,-1,2),powered(2,1,3),conj(box(30),{'expr':'x+y','modulus':5,'relation':'<','value':3}),point_limit=2000)
        expected=[(x,y) for x in range(-30,31) for y in range(-30,31) if (3*x-1)**2==(2*y+1)**3 and (x+y)%5<3]
        self.assertEqual(r['points'],expected);self.assertTrue(verify_curve_query(r))

    def test_query_tampering_and_expansion_limits(self):
        r=query_curve([0,0,1],[0,0,0,1],box(5),objective='y');r['optimization']['value']='99';self.assertFalse(verify_curve_query(r))
        with self.assertRaises(WorkLimit):query_curve([0,0,1],[0,0,0,1],objective='x**64')
        with self.assertRaises(WorkLimit):query_curve(powered(1009,1,2),powered(1,0,3),period_limit=100)

    def test_whole_query_affine_images_and_model(self):
        s=smt('xy',['(= (* (+ (* 3 x) (- 1)) (+ (* 3 x) (- 1))) (* (+ (* 2 y) 1) (+ (* 2 y) 1) (+ (* 2 y) 1)))','(< x 30)','(>= x (- 200))','(= (mod y 5) 4)'])
        r=simplify_query(s);self.assertIn('polynomial_charts',[p['method'] for p in r['steps']]);self.assertIn('QF_LIA',r['residual']);self.assertTrue(verify_simplification(r))
        # t=7 survives only in the negative x chart, at (-114,24).
        _,atoms=_parse_integer_query(r['residual'].replace('QF_LIA','QF_NIA',1));valid=[t for t in range(40) if all(_eval(a,{'_pp_curve':t}) for a in atoms)]
        self.assertEqual(valid,[7])
        for t in valid:
            model=lift_model(r,{'_pp_curve':t});self.assertEqual((3*model['x']-1)**2,(2*model['y']+1)**3);self.assertEqual(model['y']%5,4)
        with self.assertRaises(ValueError):lift_model(r,{'_pp_curve':0})

    def test_whole_query_unsupported_extra_coordinate_preserved(self):
        s=smt('xyz',['(= (* x x) (* y y))','(= z (+ x y))','(> z 100)'])
        r=simplify_query(s);self.assertTrue(verify_simplification(r))


class GammaLatticeTests(unittest.TestCase):
    def test_fixed_binomial_domains_and_optimization_with_congruences(self):
        p=mod([0,1],7,'=',4);spec={'kind':'binomial','width':2}
        d=gamma_domain(spec,'<=',100,predicate=p)
        self.assertEqual(d['domain']['cardinality'],2);self.assertTrue(verify_gamma_domain(d))
        r=optimize_gamma(spec,p);self.assertEqual(r['value'],'6');self.assertEqual(r['optimizers'],{'kind':'points','values':[4]});self.assertTrue(verify_gamma_optimum(r))


class FiniteImageTests(unittest.TestCase):
    def test_nonlinear_power_family_closes_through_mordell_image(self):
        from perfectpower.arithmetic_engine import ArithmeticEngine,verify_result
        r=ArithmeticEngine().solve([1,0,-2,0,1],3)
        self.assertEqual(r['proof']['kind'],'family_refinement');self.assertEqual(r['points'],[(-3,4),(-1,0),(0,1),(1,0),(3,4)])
        self.assertTrue(verify_result(json.loads(json.dumps(r))))
        r['proof']['refinement']['charts'][0]['parameters'].pop();self.assertFalse(verify_result(r))

    def test_finite_nonlinear_curve_optimization_three_ties(self):
        r=query_curve([1,0,-2,0,1],[0,0,0,1],objective='x*x+y*y')
        self.assertEqual(r['schema'],'pp-finite-curve-query/1');self.assertEqual(r['solution_count'],5)
        self.assertEqual(r['optimization']['optimizer_points'],[(-1,0),(0,1),(1,0)]);self.assertTrue(verify_curve_query(r))

    def test_finite_sign_domain_disconnected_search(self):
        from perfectpower.polynomial_images import sign_domain_solve,verify_sign_solve
        # -(x^2-1)(x^2-9) is nonnegative only near the two separated lobes.
        f=[-9,0,10,0,-1];r=sign_domain_solve(f)
        expected=[]
        from perfectpower.core import integer_power_root
        for x in range(-8,9):
            v=integer_power_root(-(x*x-1)*(x*x-9),2)
            if v is not None:expected.extend((x,y) for y in sorted({v,-v}))
        self.assertEqual(r['points'],expected);self.assertEqual(len(r['proof']['domain']['intervals']),2);self.assertTrue(verify_sign_solve(r))
        r['proof']['domain']['intervals'].pop();self.assertFalse(verify_sign_solve(r))

    def test_sign_domain_giant_translation_no_long_range_scan(self):
        from perfectpower.polynomial_images import sign_domain_solve,verify_sign_solve
        h=10**60;f=[1-h*h,2*h,-1];r=sign_domain_solve(f)
        self.assertEqual(r['points'],[(h-1,0),(h,-1),(h,1),(h+1,0)]);self.assertTrue(verify_sign_solve(r))
        self.assertLessEqual(r['statistics']['candidates_checked'],3)

    def test_arithmetic_family_evaluation_and_scaled_content(self):
        from perfectpower.arithmetic_engine import ArithmeticEngine,verify_result
        from perfectpower.arithmetic_families import family_points,verify_family_evaluation
        f=list(map(int,P.power(P.poly([1,1,0,0,1]),2)))
        for scale in (1,8):
            source=ArithmeticEngine().solve([scale*c for c in f],3)
            self.assertEqual(source['status'],'GENERATOR');self.assertTrue(verify_result(source))
            result=family_points(source,1);self.assertEqual(result['points'],[(-1,1 if scale==1 else 2),(0,1 if scale==1 else 2)])
            self.assertTrue(verify_family_evaluation(source,json.loads(json.dumps(result))))
            result['points'].pop();self.assertFalse(verify_family_evaluation(source,result))

    def test_supplied_generator_pullback_has_all_fibres(self):
        from perfectpower.simplifier import polynomial_pullback,verify_pullback
        r=polynomial_pullback([0,0,1],[0,-1,1],3)
        self.assertEqual(r['status'],'GENERATOR');self.assertTrue(verify_pullback(r))

    def test_nonlinear_evaluation_replay_catches_missing_root(self):
        from perfectpower.polynomial_charts import verify_evaluation
        c=parameterize_relation([1,0,-2,0,1],[1,0,-2,0,1]);e=evaluate_parameterization(c,0)
        self.assertTrue(verify_evaluation(c,e));e['charts'][0]['fibres'][0]['certificate']['roots'].pop()
        self.assertFalse(verify_evaluation(c,e))


if __name__=='__main__':unittest.main()
