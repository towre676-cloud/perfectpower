import itertools
import json
import random
import unittest
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
from unittest.mock import patch
from perfectpower.planning import CompletionPlanner,optimize_allocation
from perfectpower.planning_native import available,NativeIndex
from perfectpower.planning_cli import execute
from perfectpower.divisor_square import WorkLimit

class HybridTests(unittest.TestCase):
    def spec(self,n=7):
        rng=random.Random(n)
        return {'kind':'allocation','resources':[{'name':'a','min':1,'max':8},{'name':'b','min':2,'max':9}],
                'variables':[{'name':str(i),'costs':[rng.randrange(4),rng.randrange(4)],'profit':str(Q(rng.randrange(-4,5),3)),'upper':1} for i in range(n)]}
    @unittest.skipUnless(available(),'C++17 compiler unavailable')
    def test_native_exhaustive_differential(self):
        for seed in range(32):
            s=self.spec(1+seed%10);rng=random.Random(seed)
            for v in s['variables']:v['costs']=[rng.randrange(5),rng.randrange(5)];v['profit']=str(Q(rng.randrange(-5,6),7))
            reference=CompletionPlanner(dict(s,strategy='enumeration'));p=CompletionPlanner(dict(s,strategy='mitm'))
            self.assertEqual(reference.count(),p.count());self.assertEqual(reference.optimize(),p.optimize())
            for optimal in (False,True):
                points=reference.page(size=256,optimal=optimal)
                self.assertEqual(points,p.page(size=256,optimal=optimal))
                for i,x in enumerate(points):self.assertEqual(p.rank(x,optimal=optimal),i)
            for prefix in itertools.product((0,1),repeat=min(3,len(s['variables']))):self.assertEqual(reference.completions(prefix),p.completions(prefix))
            r=optimize_allocation(s);self.assertEqual(r['maximum'],reference.optimize()['maximum'])
            if r['point'] is not None:self.assertEqual(reference.completions(r['point'])['maximum'],r['maximum'])
    def test_weighted_symmetry(self):
        for n in range(1,10):
            s=self.spec(n)
            for i,v in enumerate(s['variables']):v['costs']=[i%2,1];v['profit']=str(Q(i%2-1,3))
            a=CompletionPlanner(dict(s,strategy='enumeration'));b=CompletionPlanner(dict(s,strategy='symmetry'))
            self.assertEqual(a.count(),b.count());self.assertEqual(a.optimize(),b.optimize())
            for prefix in itertools.product((0,1),repeat=min(3,n)):self.assertEqual(a.completions(prefix),b.completions(prefix))
            for optimal in (False,True):
                self.assertEqual(a.page(size=256,optimal=optimal),b.page(size=256,optimal=optimal))
                for i,x in enumerate(b.page(size=256,optimal=optimal)):self.assertEqual(b.rank(x,optimal=optimal),i)
    def test_huge_orbit_weights(self):
        s={'kind':'allocation','resources':[{'name':'r','max':32}], 'variables':[{'name':str(i),'costs':[1],'profit':1,'upper':1} for i in range(64)]}
        p=CompletionPlanner(s);self.assertEqual(p.strategy,'symmetry');self.assertEqual(p.count(),sum(comb(64,k) for k in range(33)))
        self.assertEqual(p.optimize()['maximizer_count'],comb(64,32))
        for optimal in (False,True):
            total=p.root_entry.optimal_count if optimal else p.count()
            for rank in (0,total//2,total-1):self.assertEqual(p.rank(p.select(rank,optimal),optimal),rank)
        s['resources'][0]['max']=64;p=CompletionPlanner(s);self.assertEqual(p.count(),2**64)
    @unittest.skipUnless(available(),'C++17 compiler unavailable')
    def test_budgets_errors_and_native_baseline(self):
        s=self.spec(8);p=CompletionPlanner(dict(s,strategy='mitm'));baseline=NativeIndex(p,exhaustive=True)
        for prefix in itertools.product((0,1),repeat=3):
            r=baseline.query(prefix);e=p.completions(prefix)
            self.assertEqual(r['count'],e['count']);self.assertEqual(r['ties'],e['maximizer_count'])
        for limits in ({'native_record_limit':1},{'native_visit_limit':1}):
            with self.assertRaises(WorkLimit):CompletionPlanner(dict(s,strategy='mitm',**limits))
        with self.assertRaises(WorkLimit):optimize_allocation(dict(s,native_visit_limit=1))
        with self.assertRaises(ValueError):p.completions([True])
        with self.assertRaises(ValueError):p.select(True)
        with self.assertRaises(ValueError):p.rank([0])
        x=p.select(0);original=list(x);x[0]=1-x[0];self.assertEqual(p.select(0),original)
        with self.assertRaises(ValueError):p.rank([bool(v) for v in original])
        with self.assertRaises(WorkLimit):CompletionPlanner(dict(s,strategy='mitm',variables=[dict(v,profit=str(2**80)) for v in s['variables']]))
        with patch('perfectpower.planning_native.available',return_value=False):self.assertNotEqual(CompletionPlanner(self.spec(6)).strategy,'mitm')
    @unittest.skipUnless(available(),'C++17 compiler unavailable')
    def test_optimization_request(self):
        s=self.spec(8);r=execute({'specification':s,'queries':[],'optimization_only':True});self.assertTrue(r['optimal']);self.assertNotIn('maximizer_count',r)
        with self.assertRaises(ValueError):execute({'specification':s,'queries':[{'method':'count'}],'optimization_only':True})
        with self.assertRaises(ValueError):execute({'specification':s,'queries':[],'optimization_only':1})
    def test_optional_compiler_fallback(self):
        s=self.spec(15)
        with patch('perfectpower.planning_native.NativeIndex',side_effect=WorkLimit('optional native planner compilation failed')):
            p=CompletionPlanner(s)
            self.assertIn(p.strategy,('gray','dp'))

    def test_invalid_symmetries(self):
        s=self.spec(3);s['strategy']='symmetry';s['variables'][0]['upper']=2
        with self.assertRaises(ValueError):CompletionPlanner(s)
        s=self.spec(8);s['strategy']='symmetry';s['state_limit']=1
        with self.assertRaises(WorkLimit):CompletionPlanner(s)

if __name__=='__main__':unittest.main()
