import copy
import json
import math
import os
import random
import unittest
from perfectpower.checked_nonlinear_population import nonlinear_population_certificate,check_nonlinear_population
from perfectpower.checked_pell_population import pell_population_certificate,check_pell_population
from perfectpower.divisor_square import WorkLimit


class ExtendedPopulationTests(unittest.TestCase):
    def test_nonlinear_all_fibres_and_expansion(self):
        for family,cs,points in [
            ('mordell_minus2',[2,0,1],[[-1,-5],[1,-5],[-1,5],[1,5]]),
            ('mordell_minus2',[3,0,0,0,1],[[0,-5],[0,5]]),
            ('mordell_minus4',[1,0,1],[[-1,-2],[1,-2],[-1,2],[1,2],[-2,-11],[2,-11],[-2,11],[2,11]])]:
            p=nonlinear_population_certificate(cs,[{'objective':['pow','y',2],'ranks':[0,100]}],family=family)
            self.assertEqual(p['source_points'],points)
            for x in range(-8,9):
                u=sum(c*x**i for i,c in enumerate(cs))
                self.assertEqual(sum(c*x**i for i,c in enumerate(p['original_coefficients'])),u**3-(2 if family.endswith('2') else 4))
            self.assertEqual(p,json.loads(json.dumps(p)))
        p=nonlinear_population_certificate([2,0,1],[{}],domain='positive')
        self.assertEqual(p['source_points'],[[1,-5],[1,5]])
        self.assertEqual(nonlinear_population_certificate([0,0,1],[{}])['source_points'],[])

    def test_random_original_equations(self):
        rng=random.Random(7348)
        for _ in range(25):
            cs=[rng.randint(-5,5),rng.randint(-3,3),rng.choice([-2,-1,1,2])]
            family=rng.choice(['mordell_minus2','mordell_minus4']);k=2 if family.endswith('2') else 4
            p=nonlinear_population_certificate(cs,[{}],family=family)
            expected=[]
            for x in range(-30,31):
                value=sum(c*x**i for i,c in enumerate(cs))**3-k
                if value>=0:
                    y=math.isqrt(value)
                    if y*y==value:expected.extend([[x,z] for z in sorted({-y,y})])
            self.assertEqual(sorted(p['source_points']),sorted(expected))

    def test_pell_cutoff_boundaries_and_global_ranks(self):
        for cutoff in [0,1,2,3,11,12,13,69,70,1000]:
            p=pell_population_certificate(cutoff,[{'objective':'x','ranks':[0,100]}],global_ranks=[0,1,4])
            expected=[]
            for x in range(cutoff+1):
                y=math.isqrt(2*x*x+1)
                if y*y==2*x*x+1:expected.append([x,y])
            self.assertEqual(p['source_points'],expected)
            self.assertGreater(p['next_point'][0],cutoff)
            self.assertEqual(p['global_selections'][-1],dict(rank=4,point=[408,577]))
            self.assertEqual(p['results'][0]['minimum'],dict(value=0,points=[[0,1]]))
        p=pell_population_certificate(10**30,[{'condition':['mod','x',0,2]}])
        self.assertLess(p['source_count'],50)
        self.assertTrue(all(x%2==0 for x,y in p['results'][0]['points']))

    def test_limits_and_mutation_rejection(self):
        for cs in [[3],[3,0],[],[True,1]]:
            with self.assertRaises(ValueError):nonlinear_population_certificate(cs,[{}])
        with self.assertRaises(WorkLimit):nonlinear_population_certificate([10**30,0,1],[{}])
        for cutoff in [-1,True,2**128]:
            with self.assertRaises(ValueError):pell_population_certificate(cutoff,[{}])
        with self.assertRaises(ValueError):pell_population_certificate(10,[{}],global_ranks=[129])
        for p,check in [(nonlinear_population_certificate([2,0,1],[{}]),check_nonlinear_population),
                        (pell_population_certificate(100,[{}]),check_pell_population)]:
            for k in ['source_points','results','lean','scope']:
                q=copy.deepcopy(p);q[k]=None
                self.assertFalse(check(q,lean='missing')['accepted'])

    def test_dispatch(self):
        from perfectpower.query_service import dispatch
        for op,args,builder in [
            ('checked_nonlinear_population',dict(coefficients=[2,0,1],queries=[{}]),nonlinear_population_certificate),
            ('checked_pell_population',dict(cutoff=100,queries=[{}]),pell_population_certificate)]:
            self.assertEqual(dispatch(None,dict(op=op,args=args)),builder(**args))

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_LEAN') and os.environ.get('LEAN_PATH'),'Lean and Mathlib required')
    def test_actual_kernel(self):
        queries=[{'objective':['pow','y',2],'ranks':[0,1,8]}, {'condition':['le',1,'x'],'objective':['mul','x','y']}]
        cases=[(nonlinear_population_certificate([2,0,1],queries),check_nonlinear_population),
               (nonlinear_population_certificate([3,0,0,0,1],queries),check_nonlinear_population),
               (nonlinear_population_certificate([1,0,1],queries,family='mordell_minus4'),check_nonlinear_population),
               (nonlinear_population_certificate([0,0,1],queries),check_nonlinear_population),
               (pell_population_certificate(1000,queries,global_ranks=[0,4,8]),check_pell_population)]
        for p,check in cases:
            r=check(p)
            self.assertTrue(r['accepted'],r)
            self.assertFalse(r['execution_verified'])


if __name__=='__main__':unittest.main()
