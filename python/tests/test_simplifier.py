import copy
import json
import unittest
from perfectpower.simplifier import (analyze_power,verify_analysis,answer_points,
    simplify_query,verify_simplification,polynomial_pullback,verify_pullback)
from perfectpower.residue_cover import evaluate
from perfectpower.core import integer_power_root


def query(names,atoms):
    return '(set-logic QF_NIA)'+''.join(f'(declare-const {n} Int)' for n in names)+''.join(f'(assert {a})' for a in atoms)+'(check-sat)'


class SimplifierTests(unittest.TestCase):
    def test_unresolved_bounded_matches_independent_scan(self):
        f=[1,1]+[0]*62+[1]
        r=analyze_power(f,10,interval=[-30,30])
        self.assertEqual(r['global']['status'],'UNRESOLVED')
        expected=[]
        for x in range(-30,31):
            y=integer_power_root(evaluate(f,x),10)
            if y is not None:expected.extend((x,v) for v in sorted({y,-y}))
        self.assertEqual(r['bounded']['points'],expected)
        self.assertTrue(verify_analysis(json.loads(json.dumps(r))))
        r['residual']=None
        self.assertFalse(verify_analysis(r))

    def test_bounded_question_scope_and_witness(self):
        r=analyze_power([1,1]+[0]*62+[1],10,interval=[-3,3])
        q=answer_points(r,{'coordinate':'x','op':'<=','value':3})
        self.assertEqual(q['scope'],{'x_interval':[-3,3]})
        self.assertEqual(q['answer'],'ALL')
        q=answer_points(r,{'coordinate':'x','op':'<=','value':-4})
        self.assertEqual(q['answer'],'COUNTEREXAMPLE')
        self.assertIn(tuple(q['witness']),r['bounded']['points'])

    def test_compact_parameter_then_whole_system_substitution(self):
        s=query('xyz',['(= (* x x) (* y y y))','(= z (+ x 1))','(> z 3)'])
        r=simplify_query(s)
        self.assertEqual([p['method'] for p in r['steps']],['square_cube','substitution','univariate_domain'])
        self.assertEqual(sum(p['variables_removed'] for p in r['steps']),2)
        self.assertIn('(>= _pp_power 2)',r['residual'])
        self.assertTrue(verify_simplification(r))
        r['residual']=r['residual'].replace('>= _pp_power 2','>= _pp_power 3')
        self.assertFalse(verify_simplification(r))

    def test_lattice_keeps_integer_image(self):
        s=query('xy',['(= (+ (* 2 x) (* 4 y)) 1)','(> (* x x) 0)'])
        r=simplify_query(s)
        self.assertIn('(assert false)',r['residual'])
        self.assertTrue(verify_simplification(r))

    def test_nonlinear_outer_not_cancelled(self):
        s=query('xy',['(= (* x x) (* y y))','(distinct x y)'])
        r=simplify_query(s)
        self.assertEqual(r['status'],'UNCHANGED')
        self.assertEqual(r['residual'],s)

    def test_pullback_all_integer_fibres(self):
        r=polynomial_pullback([1,0,0,0,1],[0,1,1])
        self.assertEqual(r['status'],'COMPLETE')
        self.assertEqual(r['points'],[(-1,-1),(-1,1),(0,-1),(0,1)])
        self.assertTrue(verify_pullback(json.loads(json.dumps(r))))
        r['points'].pop()
        self.assertFalse(verify_pullback(r))
        with self.assertRaises(ValueError):polynomial_pullback([1],[0])

    def test_budget_does_not_advertise_partial_complete(self):
        r=analyze_power([1,1]+[0]*62+[1],10,interval=[-100,100],work_limit=1)
        self.assertEqual(r['bounded']['status'],'UNRESOLVED')
        self.assertNotIn('points',r['bounded'])
        self.assertTrue(verify_analysis(r,work_limit=1))

    def test_rejects_bad_sorts_and_quantifiers(self):
        for s in [query('x',['(= x true)']),query('x',['(forall ((y Int)) (= x y))'])]:
            with self.assertRaises(ValueError):simplify_query(s)

    def test_general_coprime_powers_with_negative_witness(self):
        s=query('xy',['(= (* x x x) (* y y y y y))','(< x 0)'])
        r=simplify_query(s)
        self.assertEqual(r['steps'][0]['method'],'coprime_power')
        self.assertIn('(<= _pp_power (- 1))',r['residual'])
        self.assertTrue(verify_simplification(r))

    def test_host_receives_local_restrictions(self):
        s=query('xy',['(= (* y y) (+ (* x x x) x 1))'])
        r=simplify_query(s)
        self.assertTrue(r['necessary'])
        self.assertIn('(mod x',r['residual'])
        self.assertTrue(verify_simplification(r))

    def test_unique_observable_complete_scope(self):
        r=analyze_power([1,0,0,0,1],2)
        q=answer_points(r,{'coordinate':'x','op':'unique'})
        self.assertEqual(q['answer'],'UNIQUE')
        self.assertEqual(q['values'],[0])
        self.assertEqual(q['scope'],'all integers')

    def test_reverse_lift_validates_whole_original_system(self):
        from perfectpower.simplifier import lift_model
        s=query('xyz',['(= (* x x) (* y y y))','(= z (+ x 1))','(> z 3)'])
        r=simplify_query(s)
        self.assertEqual(lift_model(r,{'_pp_power':2}),{'x':8,'y':4,'z':9})
        with self.assertRaises(ValueError):lift_model(r,{'_pp_power':0})

    def test_fresh_parameter_collision(self):
        s=query(['x','y','_pp_power'],['(= (* x x) (* y y y))','(> _pp_power x)'])
        r=simplify_query(s)
        self.assertIn('(declare-const _pp_power_ Int)',r['residual'])

    def test_z3_query_equivalence_examples(self):
        import z3
        examples=[query('xy',['(= (+ (* 2 x) (* 4 y)) 1)']),
                  query('xyz',['(= z (+ x 1))','(= (* x x) (* y y y))','(> z 3)']),
                  query('xy',['(= x (+ y 1))','(= x y)'])]
        for s in examples:
            reduced=simplify_query(s)['residual']
            def check(script):
                solver=z3.Solver();solver.set(timeout=5000)
                solver.from_string(script);return solver.check()
            self.assertEqual(check(s),check(reduced))
