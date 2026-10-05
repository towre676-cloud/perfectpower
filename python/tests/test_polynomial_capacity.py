import copy
import json
import random
import unittest
from fractions import Fraction as Q
from perfectpower import polyalg as P
from perfectpower.decomposition import compose
from perfectpower.residue_cover import evaluate
from perfectpower.divisor_square import WorkLimit
from perfectpower.polynomial_composition import (discover_decompositions,verify_decomposition,
    PolynomialCompiler,verify_compiled)
from perfectpower.polynomial_domains import (integer_domain,verify_domain,contains,
    optimize_polynomial,verify_optimization,project_univariate_query)
from perfectpower.polynomial_relations import solve_relation,verify_relation
from perfectpower.arithmetic_engine import ArithmeticEngine,verify_result
from perfectpower.simplifier import simplify_query,lift_model,verify_simplification


def atom(f,relation):return {'poly':list(f),'relation':relation}


def truth(predicate,n):
    if type(predicate) is bool:return predicate
    if 'poly' in predicate:
        v=sum(c*n**i for i,c in enumerate(predicate['poly']));op=predicate['relation']
        return {'=':v==0,'!=':v!=0,'<':v<0,'<=':v<=0,'>':v>0,'>=':v>=0}[op]
    values=[truth(p,n) for p in predicate['args']]
    return all(values) if predicate['op']=='and' else any(values) if predicate['op']=='or' else not values[0]


def query(names,assertions):
    return '(set-logic QF_NIA)'+''.join(f'(declare-const {n} Int)' for n in names)+''.join(f'(assert {a})' for a in assertions)+'(check-sat)'


class GammaPolynomialTests(unittest.TestCase):
    def test_domains_keep_natural_index_and_exact_threshold(self):
        from perfectpower.gamma_polynomial import gamma_domain,verify_gamma_domain
        spec={'kind':'binomial','width':2}
        r=gamma_domain(spec,'<=','3');self.assertEqual(r['domain']['intervals'],[[0,3]])
        self.assertTrue(verify_gamma_domain(json.loads(json.dumps(r))))
        r=gamma_domain(spec,'<=','1/2');self.assertEqual(r['domain']['intervals'],[[0,1]])
        r['normalization']['denominator']=1;self.assertFalse(verify_gamma_domain(r))
        with self.assertRaises(ValueError):gamma_domain(spec,'<=',0.5)
        with self.assertRaises(ValueError):gamma_domain({'kind':'gamma_shift','b':0,'shift':2})

    def test_optima_rational_values_ties_empty_and_unbounded(self):
        from perfectpower.gamma_polynomial import optimize_gamma,verify_gamma_optimum
        spec={'kind':'binomial','width':2}
        r=optimize_gamma(spec);self.assertEqual((r['value'],r['optimizers']),('0',[[0,1]]))
        self.assertTrue(verify_gamma_optimum(json.loads(json.dumps(r))))
        bounded={'op':'and','args':[atom([-4,1],'>='),atom([-4,1],'<=')]}
        r=optimize_gamma({'kind':'binomial','width':3},bounded)
        self.assertEqual((r['value'],r['optimizers']),('4',[[4,4]]));self.assertTrue(verify_gamma_optimum(r))
        r=optimize_gamma({'kind':'gamma_shift','a':0,'b':3,'shift':2})
        self.assertEqual((r['value'],r['optimizers']),('12',[[0,None]]));self.assertTrue(verify_gamma_optimum(r))
        self.assertEqual(optimize_gamma(spec,sense='max')['status'],'UNBOUNDED')
        self.assertEqual(optimize_gamma(spec,False)['status'],'EMPTY')
        r=optimize_gamma(spec);r['optimizers']=[[0,0]];self.assertFalse(verify_gamma_optimum(r))


class PolynomialCompositionTests(unittest.TestCase):
    def test_random_nonmonic_compositions_discovered(self):
        rng=random.Random(987120)
        for i in range(60):
            m=2+i%4;k=2+i%3
            inner=[rng.randint(-6,6) for _ in range(m)]+[rng.choice((-3,-2,1,2,3))]
            outer=[rng.randint(-6,6) for _ in range(k)]+[rng.choice((-3,-1,1,2))]
            f=tuple(map(int,compose(outer,inner)))
            receipt=discover_decompositions(f)
            self.assertIn(m,[r['inner_degree'] for r in receipt['decompositions']])
            self.assertTrue(all(verify_decomposition(f,r) for r in receipt['decompositions']))

    def test_indecomposable_and_collision_degrees(self):
        self.assertEqual(discover_decompositions([1,1,0,0,0,0,1])['decompositions'],[])
        # Chebyshev T6 has right components in both degrees 2 and 3.
        r=discover_decompositions([-1,0,18,0,-48,0,32])
        self.assertEqual([d['inner_degree'] for d in r['decompositions']],[2,3])
        r['decompositions'][0]['outer'][0]='999'
        self.assertFalse(verify_decomposition(r['coefficients'],r['decompositions'][0]))

    def test_nonlinear_mordell_pullback_and_every_sign(self):
        # T(x)-3=(x-2)(x+1)(x+3); all three integer fibres survive.
        inner=[-3,-5,2,1];f=tuple(map(int,compose([-2,0,0,1],inner)))
        r=PolynomialCompiler().solve(f)
        self.assertEqual(r['points'],[(x,y) for x in (-3,-1,2) for y in (-5,5)])
        self.assertEqual(r['proof']['kind'],'polynomial_composition')
        self.assertTrue(verify_compiled(json.loads(json.dumps(r))))
        self.assertEqual(ArithmeticEngine().solve(f)['points'],r['points'])
        self.assertTrue(verify_result(ArithmeticEngine().solve(f)))
        bad=copy.deepcopy(r);bad['proof']['fibres'][0]['certificate']['roots'].pop()
        self.assertFalse(verify_compiled(bad))

    def test_no_integer_image_does_not_inherit_outer_points(self):
        f=tuple(map(int,compose([-2,0,0,1],[0,0,1])))
        r=PolynomialCompiler().solve(f)
        self.assertEqual(r['points'],[]);self.assertTrue(verify_compiled(r))

    def test_content_scale_transport(self):
        r=PolynomialCompiler().solve([-32,0,0,16])
        self.assertEqual(r['points'],[(3,-20),(3,20)])
        self.assertTrue(verify_compiled(r))
        r['proof']['root']=3;self.assertFalse(verify_compiled(r))

    def test_shared_budgets_never_return_partial_lists(self):
        with self.assertRaises(WorkLimit):discover_decompositions([1]*17,algebra_limit=1)
        f=tuple(map(int,compose([-2,0,0,1],[-3,-5,2,1])))
        r=PolynomialCompiler(work_limit=1).solve(f)
        self.assertEqual(r['status'],'UNRESOLVED');self.assertIsNone(r['points'])

    def test_generators_stay_structured_and_unknown_stays_unknown(self):
        r=PolynomialCompiler().solve([1,2,1]);self.assertEqual(r['status'],'GENERATOR')
        self.assertTrue(verify_compiled(r))
        r=PolynomialCompiler().solve([1,1,0,0,2],2)
        self.assertEqual(r['status'],'UNRESOLVED')


class PolynomialDomainTests(unittest.TestCase):
    def test_random_boolean_domains_against_independent_evaluation(self):
        rng=random.Random(113582)
        relations=('=','!=','<','<=','>','>=')
        for i in range(80):
            atoms=[atom([rng.randint(-8,8) for _ in range(1+rng.randrange(6))]+[rng.choice((-2,-1,1,2))],rng.choice(relations)) for _ in range(3)]
            predicate={'op':'or','args':[{'op':'and','args':atoms[:2]},{'op':'not','args':[atoms[2]]}]}
            r=integer_domain(predicate)
            self.assertTrue(verify_domain(json.loads(json.dumps(r))))
            self.assertEqual([n for n in range(-80,81) if contains(r,n)],[n for n in range(-80,81) if truth(predicate,n)])

    def test_repeated_and_noninteger_roots_in_same_unit_interval(self):
        f=tuple(map(int,P.mul(P.power(P.poly([-1,2]),2),P.poly([-2,3]))))
        r=integer_domain(atom(f,'>'))
        self.assertEqual(r['intervals'],[[1,None]])
        self.assertTrue(verify_domain(r))

    def test_giant_integer_endpoints_without_interval_scan(self):
        h=10**80
        r=integer_domain(atom([h*(h+3),-2*h-3,1],'<='))
        self.assertEqual(r['intervals'],[[h,h+3]])
        self.assertEqual(r['cardinality'],4);self.assertLess(r['root_nodes'],2000)
        self.assertTrue(verify_domain(r))

    def test_constants_empty_boolean_nodes_and_budget(self):
        for p,expected in ((True,[[None,None]]),(False,[]),(atom([0],'='),[[None,None]]),
                           ({'op':'and','args':[]},[[None,None]]),({'op':'or','args':[]},[])):
            r=integer_domain(p);self.assertEqual(r['intervals'],expected);self.assertTrue(verify_domain(r))
        with self.assertRaises(WorkLimit):integer_domain(atom([-2,0,1],'>'),node_limit=1)
        for p in ({'poly':[True],'relation':'='},{'op':'not','args':[]},{'poly':[1],'relation':'bad'}):
            with self.assertRaises(ValueError):integer_domain(p)

    def test_missing_tree_and_sign_cell_detected(self):
        r=integer_domain(atom([-2,0,1],'>'))
        bad=copy.deepcopy(r);bad['root_certificates'][0]['nodes'].pop();self.assertFalse(verify_domain(bad))
        bad=copy.deepcopy(r);bad['intervals']=[[None,None]];self.assertFalse(verify_domain(bad))

    def test_degree64_boolean_capacity(self):
        r=integer_domain(atom([-1]+[0]*63+[1],'='))
        self.assertEqual(r['intervals'],[[-1,-1],[1,1]]);self.assertTrue(verify_domain(r))


class PolynomialOptimizationTests(unittest.TestCase):
    def test_random_integer_optimization_and_every_tie(self):
        rng=random.Random(62534)
        for i in range(100):
            f=[rng.randint(-5,5) for _ in range(1+rng.randrange(6))]
            p={'op':'and','args':[atom([20,1],'>='),atom([-20,1],'<='),
                                 {'op':'or','args':[atom([-2,1],'<='),atom([-5,1],'>=')]}]}
            sense='min' if i%2 else 'max'
            r=optimize_polynomial(p,f,sense=sense)
            domain=[n for n in range(-20,21) if truth(p,n)]
            value=(min if sense=='min' else max)(sum(c*n**j for j,c in enumerate(f)) for n in domain)
            expected=[n for n in domain if sum(c*n**j for j,c in enumerate(f))==value]
            actual=[n for lo,hi in r['optimizers'] for n in range(lo,hi+1)]
            self.assertEqual(r['value'],value);self.assertEqual(actual,expected)
            self.assertTrue(verify_optimization(json.loads(json.dumps(r))))

    def test_huge_translated_optimum_and_adjacent_ties(self):
        h=10**60
        f=tuple(map(int,P.power(P.poly([h*(h+1),-2*h-1,1]),2)))
        r=optimize_polynomial(True,f)
        self.assertEqual(r['value'],0);self.assertEqual(r['optimizers'],[[h,h+1]])
        self.assertLess(r['root_nodes'],2500);self.assertTrue(verify_optimization(r))

    def test_unbounded_empty_constant_and_tail_restrictions(self):
        self.assertEqual(optimize_polynomial(True,[0,1])['status'],'UNBOUNDED')
        self.assertEqual(optimize_polynomial(True,[0,0,1],sense='max')['status'],'UNBOUNDED')
        r=optimize_polynomial(atom([-7,1],'>='),[0,1]);self.assertEqual(r['value'],7)
        r=optimize_polynomial(False,[0,1]);self.assertEqual(r['status'],'EMPTY');self.assertTrue(verify_optimization(r))
        r=optimize_polynomial(atom([-2,0,1],'>='),[9]);self.assertEqual(r['optimizers'],[[None,-2],[2,None]])
        self.assertTrue(verify_optimization(r))

    def test_tampered_optimum_and_difference(self):
        r=optimize_polynomial(True,[0,-1,1])
        for key,value in (('value',-1),('optimizers',[[0,0]]),('difference',[0])):
            bad=copy.deepcopy(r);bad[key]=value;self.assertFalse(verify_optimization(bad))


class PolynomialRelationTests(unittest.TestCase):
    def test_nonlinear_witness_fibres(self):
        # (y^2-5)^2=x^3-2: the outer witness +5 has y=+-sqrt(10),
        # while witness -5 has y=0. Only that integer fibre remains.
        r=solve_relation([-2,0,0,1],[25,0,-10,0,1])
        self.assertEqual(r['points'],[(3,0)]);self.assertTrue(verify_relation(r))

    def test_quadratic_transport_swapped_and_both_signs(self):
        for left,right,expected in (([-2,0,0,1],[1,-4,4],[(3,-2),(3,3)]),
                                    ([1,-4,4],[-2,0,0,1],[(-2,3),(3,3)])):
            r=solve_relation(left,right);self.assertEqual(r['points'],expected)
            self.assertTrue(verify_relation(json.loads(json.dumps(r))))

    def test_affine_generator_and_noninjective_unknown(self):
        r=solve_relation([7,0,1],[-2,-3]);self.assertEqual(r['status'],'GENERATOR');self.assertTrue(verify_relation(r))
        for x in range(-10,11):
            g=r['generator'];numerator=evaluate(g['numerator'],x)
            if numerator%g['denominator']==0:self.assertEqual(x*x+7,-3*(numerator//g['denominator'])-2)
        self.assertEqual(solve_relation([0,0,1],[0,0,1])['status'],'UNRESOLVED')

    def test_whole_query_preserves_side_conditions_and_model(self):
        s=query('xyz',['(= (+ (* 4 y y) (* (- 4) y) 1) (- (* x x x) 2))','(> z x)'])
        r=simplify_query(s);self.assertIn('polynomial_relation',[p['method'] for p in r['steps']])
        self.assertTrue(verify_simplification(r));m=lift_model(r,{'z':4})
        self.assertEqual(m['x'],3);self.assertIn(m['y'],(-2,3))
        with self.assertRaises(ValueError):lift_model(r,{'z':2})

    def test_whole_univariate_query_becomes_linear_and_keeps_models(self):
        s=query('x',['(or (<= (* x x) 4) (= (* x x x) 27))'])
        r=project_univariate_query(s)
        self.assertEqual(r['domain']['intervals'],[[-2,3]])
        r=simplify_query(s);self.assertIn('QF_LIA',r['residual']);self.assertTrue(verify_simplification(r))
        self.assertEqual(lift_model(r,{'x':3}),{'x':3})
        with self.assertRaises(ValueError):lift_model(r,{'x':4})

    def test_degree64_whole_query_and_integer_boolean_implication(self):
        power='(* '+' '.join(['x']*64)+')'
        r=project_univariate_query(query('x',[f'(= {power} 1)']))
        self.assertEqual(r['domain']['intervals'],[[-1,-1],[1,1]])
        s=query('x',['(=> (> (* x x) 4) (< x 0))'])
        r=project_univariate_query(s)
        self.assertEqual(r['domain']['intervals'],[[None,2]])
        with self.assertRaises(ValueError):project_univariate_query(query('x',['(= (mod x 3) 1)']))


if __name__=='__main__':unittest.main()
