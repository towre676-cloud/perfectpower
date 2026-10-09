import copy
import os
import random
import unittest

from perfectpower.checked_population import population_certificate, check_population
from perfectpower.divisor_square import WorkLimit


class CheckedPopulationTests(unittest.TestCase):
    def test_batch_original_coordinates_and_bivariate_minimum(self):
        p=population_certificate([0,0,1],2,[-2,2],[
            {'condition':['le',0,'y'],'ranks':[0,4,5],
             'objective':['add',['pow','x',2],['pow','y',2]]},
            {'condition':['not',['mod','x',0,2]],'objective':'y'},
            {'condition':False}])
        self.assertEqual(p['source_count'],9)
        self.assertEqual(p['results'][0]['minimum'],{'value':0,'points':[[0,0]]})
        self.assertEqual(p['results'][0]['selections'][-1],{'rank':5,'point':None})
        self.assertEqual(p['results'][1]['minimum'],{'value':-1,'points':[[-1,-1],[1,-1]]})
        self.assertIsNone(p['results'][2]['minimum'])
        self.assertEqual(p['proof_status'],'emitted')
        self.assertIn('rank_roundtrip_0',p['lean'])

    def test_signed_modular_queries_against_independent_equation_scan(self):
        rng=random.Random(602)
        for _ in range(20):
            cs=[rng.randint(-3,3) for _ in range(4)]; d=rng.randint(2,5)
            m=rng.randint(1,5); r=rng.randint(-5,5)
            queries=[{'condition':['and',['mod','y',r,m],['le','x','y']],
                      'objective':['mul','x','y']}]
            p=population_certificate(cs,d,[-3,3],queries)
            expected=[[x,y] for x in range(-3,4) for y in range(-100,101)
                      if y**d==sum(c*x**i for i,c in enumerate(cs))
                      and (y-r)%m==0 and x<=y]
            self.assertEqual(p['results'][0]['points'],expected)
            if expected:
                v=min(x*y for x,y in expected)
                self.assertEqual(p['results'][0]['minimum'],dict(
                    value=v,points=[q for q in expected if q[0]*q[1]==v]))

    def test_boolean_composition_empty_and_explicit_scope(self):
        p=population_certificate([0,1],3,[-3,3],[
            {'condition':['or',['eq','x',-1],['eq','y',1]],'ranks':[0,1,2]},
            {'condition':['not',True]}],[-2,0])
        self.assertEqual(p['results'][0]['points'],[[-1,-1]])
        self.assertEqual(p['results'][1]['count'],0)
        self.assertIn('explicit integer rectangle',p['scope'])
        self.assertEqual(population_certificate([0],2,[3,2],[{}])['results'][0]['count'],0)

    def test_objective_is_query_local(self):
        for queries in ([{'objective':'y'},{}],[{}, {'objective':'y'}]):
            p=population_certificate([1],2,[0,1],queries)
            for q,result in zip(queries,p['results']):
                self.assertEqual(result['minimum'] is None,'objective' not in q)

    def test_reject_mutations_before_running_lean(self):
        p=population_certificate([0,0,1],2,[-1,1],[{'ranks':[0,9]}])
        mutations=[('results',[]),('source_count',99),('lean','axiom bad : False'),
                   ('source_sha256','0'*64),('proof_status','kernel_checked')]
        for key,value in mutations:
            q=copy.deepcopy(p);q[key]=value
            self.assertFalse(check_population(q,lean='does-not-exist')['accepted'])
        q=copy.deepcopy(p);q['specification']['queries'][0]['condition']=False
        self.assertFalse(check_population(q,lean='does-not-exist')['accepted'])

    def test_input_language_and_budgets(self):
        invalid=[{'condition':['mod','x',0,0]}, {'condition':['le',True,0]},
                 {'condition':['eq','z',0]}, {'condition':['not',True,False]},
                 {'objective':['pow','x',17]}, {'objective':['pow','x',True]},
                 {'ranks':[True]}, {'ranks':[1<<129]}, {'unknown':True}]
        for query in invalid:
            with self.assertRaises(ValueError):
                population_certificate([0],2,[0,1],[query])
        c=True
        for _ in range(34): c=['not',c]
        with self.assertRaises(WorkLimit):population_certificate([0],2,[0,1],[{'condition':c}])
        o='x'
        for _ in range(4):o=['pow',o,16]
        with self.assertRaises(WorkLimit):population_certificate([0],2,[2,2],[{'objective':o}])
        with self.assertRaises(ValueError):population_certificate([0],2,[0,1],[])

    def test_public_dispatch(self):
        from perfectpower.query_service import dispatch
        args=dict(coefficients=[0,1],exponent=3,x_bounds=[-2,2],queries=[{'objective':'y'}])
        self.assertEqual(dispatch(None,{'op':'checked_population','args':args}),population_certificate(**args))

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_LEAN'),'explicit Lean toolchain required')
    def test_actual_kernel_batches(self):
        cases=[([0,0,1],2,[-2,2],None),([0,1],3,[-3,3],None),
               ([-1],2,[-2,2],None),([0],2,[-2,2],None),
               ([1],2,[2,1],None),([-2,0,0,1],2,[-2,5],[0,6])]
        queries=[{'condition':['or',['eq','x',0],['not',['mod','y',0,2]]],
                  'objective':['add',['pow','x',2],['pow','y',2]],'ranks':[0,1,999]},
                 {'condition':['le','y',0],'objective':['mul','x','y']},
                 {'condition':False}]
        for cs,d,x,y in cases:
            p=population_certificate(cs,d,x,queries,y)
            receipt=check_population(p)
            self.assertTrue(receipt['accepted'],receipt)
            self.assertFalse(receipt['execution_verified'])
            self.assertIn('QueryNative',receipt['library_sha256'])


if __name__=='__main__':unittest.main()
