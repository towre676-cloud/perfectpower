import random
import unittest
from math import isqrt
from pathlib import Path
from tempfile import TemporaryDirectory
from perfectpower.centered_divisor import shift_polynomial,solve_centered
from perfectpower.divisor_square import solve,evaluate,WorkLimit
from perfectpower.compiler import PowerConstraint,compile_constraint,pmul,COMPLETE_FINITE
from perfectpower.square_triangular_queries import point,query,select,residue_schedule,last_index
from perfectpower.recurrence import CycleLimit
from perfectpower.showcase import build_examples,OFFSET,FILTERS,constraint_cases
from perfectpower.finite_formula import emit_finite_query

class CenteredCompleteSolving(unittest.TestCase):
    def test_huge_offset_compiles_into_complete_points(self):
        c=(0,-2,0,2);p=shift_polynomial(c,-OFFSET);f=list(pmul(p,p));f[0]+=25
        plan=compile_constraint(PowerConstraint(tuple(f),2))
        self.assertEqual(plan.status,COMPLETE_FINITE)
        self.assertEqual(plan.data['coordinate_shift'],OFFSET)
        self.assertEqual([n for n,w in plan.all_hits()],[OFFSET+t for t in range(-2,3)])
        self.assertEqual(plan.contains(OFFSET+2),[-13,13])
        self.assertEqual(plan.contains(OFFSET+3),[])
        self.assertLess(plan.data['divisor_trials'],100)
        with self.assertRaises(WorkLimit):solve(p,25,work_limit=1000)

    def test_random_shifts_preserve_all_complete_solutions(self):
        rng=random.Random(212)
        for _ in range(80):
            d=rng.randrange(1,7);c=tuple(rng.randrange(-3,4) for _ in range(d))+(rng.choice([-3,-1,1,2]),)
            s=rng.choice([-10**12,-20,0,17,10**12]);k=rng.choice([v for v in range(-25,26) if v])
            p=shift_polynomial(c,-s);r=solve_centered(p,k,shift=s);base=solve(c,k)
            self.assertEqual(r['points'],sorted((x+s,y) for x,y in base['points']))
            for n in range(-3,4):self.assertEqual(evaluate(p,n+s),evaluate(c,n))

    def test_shift_inversion_budgets_and_regression(self):
        c=(0,-1000000,1)
        r=solve_centered(c,1,work_limit=5000)
        self.assertEqual(r['coordinate_shift'],0)
        self.assertIn((1000000,1),r['points'])
        with self.assertRaises(WorkLimit):solve_centered((1,0,1),10**12,work_limit=10)
        with self.assertRaises(WorkLimit):shift_polynomial((1,)*10,1,degree_limit=4)
        with self.assertRaises(ValueError):shift_polynomial((1,2),0.5)
        with self.assertRaises(ValueError):solve_centered((1,2),0)

class SparseSizeQueries(unittest.TestCase):
    def test_counts_match_independent_integer_sqrt_scan(self):
        filters=[(),(('index',7,0),),(('root',5,1),),(('index',3,1),('root',7,2))]
        for bound in (0,1,7,8,48,49,1000,100000):
            for f in filters:
                expected=[]
                for n in range(1,bound+1):
                    v=n*(n+1)//2;t=isqrt(v)
                    if t*t==v and all((n if coord=='index' else t)%m==r%m for coord,m,r in f):expected.append((n,t))
                self.assertEqual(query(bound,f)['filtered_count'],len(expected),(bound,f))
                for i,p in enumerate(expected):self.assertEqual(select(i,f)['point'],p)

    def test_exact_huge_boundary_and_period(self):
        r=query(10**1000,FILTERS)
        self.assertEqual(r['unfiltered_count'],1307)
        self.assertEqual(r['filtered_count'],28)
        self.assertEqual(r['schedule']['period'],48)
        self.assertEqual(r['schedule']['cycle_hits'],[1])
        self.assertLessEqual(point(1307)[0],10**1000)
        self.assertGreater(point(1308)[0],10**1000)
        self.assertLessEqual(select(27,FILTERS)['point'][0],10**1000)
        self.assertGreater(select(28,FILTERS)['point'][0],10**1000)

    def test_boundary_on_exact_hits_and_two_adic_filter(self):
        for j in range(1,25):
            n,t=point(j)
            self.assertEqual(last_index(n)[0],j)
            self.assertEqual(last_index(n-1)[0],j-1)
        s=residue_schedule((('index',8,1),('root',4,1)))
        for j in range(1,4*s['period']):
            n,t=point(j)
            self.assertEqual(j%s['period'] in s['cycle_hits'],n%8==1 and t%4==1)
        with self.assertRaises(CycleLimit):residue_schedule(FILTERS,state_limit=47)
        with self.assertRaises(ValueError):query(-1)
        with self.assertRaises(ValueError):residue_schedule((('index',0,1),))

class CompleteExamples(unittest.TestCase):
    def test_end_to_end_packets_and_standalone_program(self):
        with TemporaryDirectory() as tmp:
            r=build_examples(tmp)
            self.assertEqual(len(r['hidden_needle']['complete_points']),10)
            self.assertEqual(len(r['whole_queries']),6)
            self.assertTrue(r['hidden_needle']['standalone_replayed'])
            env={};exec((Path(tmp)/'hidden_needle_program.py').read_text(),env)
            self.assertEqual(len(env['run'](OFFSET+10)),5)
            self.assertEqual(env['run'](100000),[])
            for name,source,expected in constraint_cases():
                self.assertEqual((Path(tmp)/'queries'/f'{name}.smt2').read_text(),source)

    def test_full_constraint_answers_and_model_replay(self):
        import z3
        for name,source,expected in constraint_cases():
            out=emit_finite_query(source);solver=z3.Solver();solver.add(z3.parse_smt2_string(out.smt))
            self.assertEqual(str(solver.check()),expected,name)
            if expected=='sat':
                model=solver.model();bindings=[(z3.Int(str(d)),model[d]) for d in model.decls()]
                original=z3.And(list(z3.parse_smt2_string(source)))
                self.assertTrue(z3.is_true(z3.simplify(z3.substitute(original,*bindings))),name)

class FiniteProjection(unittest.TestCase):
    def test_projection_eliminates_only_complete_relation_variables(self):
        import z3
        from perfectpower.finite_projection import project_finite_query
        from perfectpower.finite_projection import ProjectionLimit
        with self.assertRaises(ProjectionLimit):project_finite_query(next(constraint_cases())[1],branch_limit=1)
        for name,source,expected in constraint_cases():
            p=project_finite_query(source);solver=z3.Solver();solver.add(z3.parse_smt2_string(p.smt))
            self.assertEqual(str(solver.check()),expected,name)
            self.assertTrue(p.linear,name)
            for variable in p.emission.eliminated_symbols:
                self.assertNotIn(f'(declare-const {variable} ',p.smt)
            self.assertIn('(declare-const z Int)',p.smt)
            self.assertIn('(declare-const w Int)',p.smt)

    def test_remaining_variable_fibres_match_independent_original_evaluation(self):
        import z3
        from perfectpower.finite_projection import project_finite_query
        for h in (-4,0,7):
            residuals=['(= (+ z w) (+ u v))','(>= (* z z) u)',
                       '(not (= w (* u v)))','(or (= z u) (= w v))']
            for residual in residuals:
                shift=str(h) if h>=0 else f'(- {-h})'
                expr=f'(- u {shift})'
                source=f'(declare-const u Int)(declare-const v Int)(declare-const z Int)(declare-const w Int)(assert (= (* v v) (+ (* {expr} {expr} {expr}) 2)))(assert {residual})(check-sat)'
                p=project_finite_query(source)
                original=z3.And(list(z3.parse_smt2_string(source)))
                projected=z3.And(list(z3.parse_smt2_string(p.smt)))
                for zv in range(-3,4):
                    for wv in range(-3,4):
                        remaining=[(z3.Int('z'),z3.IntVal(zv)),(z3.Int('w'),z3.IntVal(wv))]
                        expected=False
                        # Complete y²=x³+2 has precisely (-1,±1), independently
                        # put through this query's shift, without the projection AST.
                        for uv,vv in ((h-1,-1),(h-1,1)):
                            bindings=remaining+[(z3.Int('u'),z3.IntVal(uv)),(z3.Int('v'),z3.IntVal(vv))]
                            expected |= z3.is_true(z3.simplify(z3.substitute(original,*bindings)))
                        actual=z3.simplify(z3.substitute(projected,*remaining))
                        self.assertEqual(z3.is_true(actual),expected,(h,residual,zv,wv))
                if '* z z' in residual:self.assertFalse(p.linear)

if __name__=='__main__':unittest.main()
