import unittest
import random
from math import isqrt
from copy import deepcopy
from perfectpower.linear_product import solve,check,query,compile_lean,close_descent,LinearProductPopulation
from perfectpower.divisor_square import WorkLimit
from perfectpower.euclid_descent import compile_descent,classify_input


class LinearProductTests(unittest.TestCase):
    def test_known_complete_signed_lists(self):
        self.assertEqual(solve([0,1],[2,1])['points'],[[-2,0],[0,0]])
        self.assertEqual(solve([0,1],[6,1])['points'],[[-8,-4],[-8,4],[-6,0],[0,0],[2,-4],[2,4]])
        self.assertEqual(solve([1,2],[6,8])['points'],[])

    def test_exhaustive_small_coefficients(self):
        cases=0
        for a in [-4,-2,-1,1,2,4]:
            for c in [-4,-2,-1,1,2,4]:
                if a*c<=0 or isqrt(a*c)**2!=a*c:continue
                for b in range(-3,4):
                    for d in range(-3,4):
                        if a*d-b*c==0:continue
                        p=solve([b,a],[d,c]);q,t=p['transform']['q'],p['transform']['t'];k=p['transform']['constant']
                        # Any uv=k has |u+v| <= k+1; hence this covers all inputs.
                        bound=(k+1+2*abs(t)+4*q-1)//(4*q)
                        brute=[]
                        for n in range(-bound,bound+1):
                            z=(a*n+b)*(c*n+d)
                            if z>=0 and isqrt(z)**2==z:
                                for y in sorted({isqrt(z),-isqrt(z)}):brute.append([n,y])
                        self.assertEqual(p['points'],brute,(a,b,c,d));cases+=1
        self.assertGreater(cases,400)

    def test_heldout_random_and_descent_bridge(self):
        r=random.Random(9051)
        for _ in range(120):
            a=r.choice([1,4,9,-1,-4,-9]);c=r.choice([1,4,9])*(1 if a>0 else -1)
            b,d=r.randint(-20,20),r.randint(-20,20)
            if a*d==b*c:continue
            p=solve([b,a],[d,c]);descent=compile_descent([b,a],[d,c])
            self.assertTrue(check(p))
            for n,y in p['points']:
                self.assertIn(classify_input(descent,n)['status'],('ZERO','BRANCH'))
                self.assertEqual(y*y,(a*n+b)*(c*n+d))
            # Factor-order symmetry and simultaneous negation are independent metamorphic checks.
            self.assertEqual(p['points'],solve([d,c],[b,a])['points'])
            self.assertEqual(p['points'],solve([-b,-a],[-d,-c])['points'])

    def test_large_translation_is_not_a_coordinate_scan(self):
        shift=10**80
        p=solve([-shift,1],[6-shift,1])
        self.assertEqual(p['points'],[[shift-8,-4],[shift-8,4],[shift-6,0],[shift,0],[shift+2,-4],[shift+2,4]])
        self.assertEqual(p['work_used'],solve([0,1],[6,1])['work_used'])

    def test_all_descent_branches_closed_including_empty_ones(self):
        p=compile_descent([0,1],[6,1]);closed=close_descent(p)
        self.assertEqual(len(closed['branches']),len(p['branches']))
        partition=closed['zero_points']+[point for branch in closed['branches'] for point in branch['points']]
        self.assertEqual(sorted(partition),closed['chart']['points'])
        self.assertEqual(len(partition),len({tuple(p) for p in partition}))
        self.assertTrue(any(not b['points'] for b in closed['branches']))
        with self.assertRaises(ValueError):close_descent(compile_descent([0,1],[6,1],3))

    def test_budget_and_unsupported_families(self):
        for left,right in [([0,1],[1,2]),([0,1],[1,-1]),([0,1],[0,4]),([0,0,1],[2,1]),([True,1],[2,1])]:
            with self.assertRaises(ValueError):solve(left,right)
        with self.assertRaises(WorkLimit):solve([0,1],[10007,1],work_limit=1)
        with self.assertRaises(WorkLimit):compile_lean(solve([0,1],[1000,1]))
        for limit in [0,-1,True]:
            with self.assertRaises(ValueError):solve([0,1],[6,1],work_limit=limit)

    def test_packets_reject_omission_and_tampering(self):
        p=solve([0,1],[6,1])
        for key in ['points','signed_divisors','accepted_pairs']:
            bad=deepcopy(p);bad[key].pop()
            with self.assertRaises(ValueError):check(bad)
        bad=deepcopy(p);bad['complete']=False
        with self.assertRaises(ValueError):check(bad)
        bad=deepcopy(p);bad['left'][0]+=1
        with self.assertRaises(ValueError):check(bad)

    def test_population_queries_and_exact_optima(self):
        p=solve([0,1],[6,1]);pop=LinearProductPopulation(p)
        for i,point in enumerate(p['points']):
            self.assertEqual(pop.select(i),tuple(point));self.assertEqual(pop.rank(point),i)
        self.assertIsNone(pop.rank([123,123]))
        self.assertEqual(query(p,{'restrictions':{'n_min':0,'y_min':0},'objective':'y','maximize':True,'select':1,'rank':[2,4]}),
                         {'count':2,'points':[[0,0],[2,4]],'selected':[2,4],'rank':1,'optimum':{'value':4,'points':[[2,4]]}})
        self.assertEqual(LinearProductPopulation(p,n_modulus=3,n_residue=2).count(),2)
        self.assertIsNone(LinearProductPopulation(p,n_min=100).optimize())
        for rank in [-1,6,True]:
            with self.assertRaises(IndexError):pop.select(rank)
        with self.assertRaises(ValueError):LinearProductPopulation(p,n_modulus=0)
        with self.assertRaises(ValueError):LinearProductPopulation(p,n_min=5,n_max=0)

    def test_cli_and_source_bound_emission(self):
        from perfectpower.euclid_cli import dispatch
        p=dispatch('solve-linear-product',{'left':[0,1],'right':[6,1]})
        self.assertEqual(p['cardinality'],6)
        self.assertEqual(dispatch('query-linear-product',{'left':[0,1],'right':[6,1],'restrictions':{'y_min':0}})['count'],4)
        source=compile_lean(p)['source']
        self.assertIn('all_integer_solutions',source)
        self.assertNotIn('sorry',source)


if __name__=='__main__':unittest.main()
