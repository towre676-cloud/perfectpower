import copy
import json
import math
import os
import random
import unittest
from perfectpower.checked_family_population import family_population_certificate,check_family_population
from perfectpower.checked_pell_family import pell_family_certificate,check_pell_family,power,fundamental_seed
from perfectpower.divisor_square import WorkLimit


class FamilyPushTests(unittest.TestCase):
    def test_square_differences_against_original_equations(self):
        rng=random.Random(8841)
        for _ in range(40):
            cs=[rng.randint(-3,3),rng.randint(-2,2),rng.choice([-2,-1,1,2])];k=rng.choice([i for i in range(-20,21) if i])
            p=family_population_certificate(cs,[{'objective':['pow','y',2],'ranks':[0,999]}],offset=k)
            expected=[]
            for x in range(-60,61):
                u=sum(c*x**i for i,c in enumerate(cs));v=u*u+k
                if v>=0:
                    y=math.isqrt(v)
                    if y*y==v:expected.extend([[x,z] for z in sorted({-y,y})])
            self.assertEqual(p['source_points'],sorted(expected))
            self.assertEqual(p,json.loads(json.dumps(p)))
            for x,y in p['source_points']:self.assertEqual(y*y,sum(c*x**i for i,c in enumerate(p['original_coefficients'])))

    def test_large_linear_and_zero_fibres(self):
        p=family_population_certificate([3,10**30],[{}],family='mordell_minus2')
        self.assertEqual(p['source_points'],[[0,-5],[0,5]])
        self.assertLess(p['divisor_work'],4)
        p=family_population_certificate([3,0,0,10**30],[{}],family='mordell_minus2')
        self.assertEqual(p['source_points'],[[0,-5],[0,5]])
        p=family_population_certificate([16,0,1],[{}],family='mordell_minus13')
        self.assertEqual(p['source_points'],[[-1,-70],[-1,70],[1,-70],[1,70]])
        for family in ['mordell_minus5','mordell_minus6','mordell_descent']:
            p=family_population_certificate([0,0,1],[{}],family=family,**({'offset':-9985} if family=='mordell_descent' else {}))
            self.assertEqual(p['source_count'],0)

    def test_general_pell_signed_and_count_only(self):
        for D in [2,3,5,6,7,8,10,11,12,13,17,19,23,29]:
            N=1000;p=pell_family_certificate(D,N,[{'ranks':[0,999]}],domain='integer')
            expected=[]
            for x in range(-N,N+1):
                y=math.isqrt(D*x*x+1)
                if y*y==D*x*x+1:expected.extend([[x,-y],[x,y]])
            self.assertEqual(sorted(p['source_points']),sorted(expected))
            direct=pell_family_certificate(D,N,global_ranks=[0,4])
            self.assertIsNone(direct['source_points'])
            self.assertEqual(direct['source_count'],(len(expected)+2)//4)
            self.assertEqual(direct['global_selections'][0]['point'],[0,1])
        p=pell_family_certificate(2,10**30,global_ranks=[1000],global_objective=['add','x','y'])
        self.assertEqual(p['source_count'],40)
        self.assertEqual(p['global_optimum']['value'],1)
        self.assertGreater(p['global_selections'][0]['point'][0].bit_length(),2000)
        self.assertEqual(pell_family_certificate(7,100,global_objective=['mul',-1,'x'])['global_optimum']['status'],'unbounded_below')

    def test_refusals_and_packet_mutations(self):
        for kwargs in [dict(offset=0),dict(domain='bad'),dict(coefficients=[1,0])]:
            spec=dict(coefficients=[0,1],queries=[{}]);spec.update(kwargs)
            with self.assertRaises(ValueError):family_population_certificate(**spec)
        with self.assertRaises(WorkLimit):family_population_certificate([10**30,0,1],[{}])
        for D in [0,1,4,9,True]:
            with self.assertRaises(ValueError):pell_family_certificate(D,10)
        with self.assertRaises(WorkLimit):pell_family_certificate(61,10)
        with self.assertRaises(WorkLimit):pell_family_certificate(2,10,global_ranks=[1000000])
        for p,check in [(family_population_certificate([0,1],[{}],offset=15),check_family_population),(pell_family_certificate(3,100),check_pell_family)]:
            for k in ['source_count','lean','scope','specification_sha256']:
                q=copy.deepcopy(p);q[k]=None;self.assertFalse(check(q,lean='missing')['accepted'])

    def test_dispatch(self):
        from perfectpower.query_service import dispatch
        for op,args,f in [('checked_family_population',dict(coefficients=[0,1],queries=[{}],offset=15),family_population_certificate),('checked_pell_family',dict(D=3,cutoff=100),pell_family_certificate)]:
            self.assertEqual(dispatch(None,dict(op=op,args=args)),f(**args))

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_LEAN') and os.environ.get('LEAN_PATH'),'Lean and Mathlib required')
    def test_actual_kernel(self):
        queries=[{'ranks':[0,1,100],'objective':['pow','y',2]}]
        for p,check in [(family_population_certificate([0,0,1],queries,offset=15),check_family_population),
                        (family_population_certificate([0,1],queries,offset=-15),check_family_population),
                        (family_population_certificate([3,10**30],queries,family='mordell_minus2'),check_family_population),
                        (family_population_certificate([16,0,1],queries,family='mordell_minus13'),check_family_population),
                        (family_population_certificate([5,0,1],queries,family='mordell_descent',offset=-9985),check_family_population),
                        (pell_family_certificate(3,100,queries,domain='integer',global_ranks=[4]),check_pell_family),
                        (pell_family_certificate(2,10**30,global_ranks=[1000],global_objective=['add','x','y']),check_pell_family),
                        (pell_family_certificate(7,100,global_objective=['mul',-1,'x']),check_pell_family)]:
            result=check(p);self.assertTrue(result['accepted'],result);self.assertFalse(result['execution_verified'])


if __name__=='__main__':unittest.main()
