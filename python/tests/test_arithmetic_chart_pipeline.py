import copy
from fractions import Fraction
import random
import unittest
from perfectpower.integer_valued_power_charts import *
from perfectpower.branching_residue_patch import *
from perfectpower.unordered_weighted_determinant import *
from perfectpower.bounded_residue_patch import evaluate


def ev(cs,x):return sum(Fraction(c)*x**i for i,c in enumerate(cs))


class PowerChartTests(unittest.TestCase):
    def test_full_signed_source_census(self):
        cases=[(['7/2',0,'1/2'],2,0),([0,'-1/2','1/2'],2,0),
               ([0,'1/6','1/6'],2,0),([0,0,'1/3'],3,2),
               (['1/2'],2,0),([0],3,0),([-2,1],3,-1)]
        for cs,d,k in cases:
            p=power_charts(cs,d,[[-15,17],[-12,13]],offset=k,factors=[[2,2],[3,1]])
            self.assertTrue(verify_power_charts(p))
            expected=[[x,y] for x in range(-15,18) for y in range(-12,14)
                      if ev(cs,x).denominator==1 and ev(cs,x)+k==y**d]
            self.assertEqual(chart_scan(p)['points'],expected)

    def test_integral_everywhere_still_has_integer_coefficient_charts(self):
        p=power_charts([0,'-1/2','1/2'],2,[[-5,5],[-5,5]])
        self.assertEqual([c['residue'] for c in p['charts']],[0,1])
        for c in p['charts']:
            for n in [-100,-3,0,4,100]:
                self.assertEqual(ev(c['coefficients'],n),ev(p['rational_coefficients'],c['residue']+2*n))

    def test_exact_bounds_and_rank_select(self):
        p=power_charts(['7/2',0,'1/2'],2,[[-9,12],[-8,7]],factors=[[2,2],[3,1]])
        points=[chart_select(p,i) for i in range(chart_population(p)['count'])]
        self.assertEqual(len(points),len(set(map(tuple,points))))
        self.assertTrue(all(-9<=x<=12 and -8<=y<=7 and x%2 for x,y in points))
        for i,z in enumerate(points):self.assertEqual(chart_rank(p,z),i)
        with self.assertRaises(IndexError):chart_select(p,len(points))
        with self.assertRaises(ValueError):chart_rank(p,[0,0])

    def test_narrow_box_inactive_charts(self):
        p=power_charts([0,'1/6','1/6'],2,[[1,1],[-5,5]])
        self.assertTrue(all(not c['active'] for c in p['charts']))
        self.assertEqual(chart_population(p)['count'],0)
        self.assertEqual(chart_scan(p)['points'],[])

    def test_duplicate_prime_and_factored_cover(self):
        cs=[0,'-1/2','1/2'];b=[[-20,20],[-20,20]]
        p=power_charts(cs,2,b,factors=[[2,1],[2,3],[3,2]],explicit_limit=1)
        q=power_charts(cs,2,b,factors=[[2,3],[3,2]],explicit_limit=100000)
        self.assertEqual(chart_scan(p)['points'],chart_scan(q)['points'])
        self.assertEqual(chart_population(p)['count'],chart_population(q)['count'])

    def test_tampering_and_budgets(self):
        p=power_charts(['7/2',0,'1/2'],2,[[-5,5],[-5,5]])
        for field,value in [('execution_verified',0),('denominator',3),('charts',[]),('extra',True)]:
            q=copy.deepcopy(p);q[field]=value;self.assertFalse(verify_power_charts(q))
        with self.assertRaises(ValueError):power_charts(['1/65'],2,[[-1,1],[-1,1]])
        with self.assertRaises(ValueError):chart_scan(p,candidate_limit=1)

    def test_composed_branching_and_query(self):
        from perfectpower.query_service import dispatch
        p=dispatch(None,{'op':'integer_power_charts','args':{'coefficients':['7/2',0,'1/2'],
                         'exponent':2,'bounds':[[-12,12]]*2}})
        q=dispatch(None,{'op':'branch_integer_power_charts','args':{'packet':p,'prime':2,'exponent':3}})
        self.assertTrue(verify_branch_power_charts(q))
        self.assertEqual(branch_power_scan(q)['points'],chart_scan(p)['points'])
        self.assertTrue(dispatch(None,{'op':'verify_branch_integer_power_charts','args':{'packet':q}})['valid'])
        empty=power_charts(['1/2'],2,[[-1,1]]*2)
        with self.assertRaises(ValueError):branch_power_charts(empty,True,2)

    def test_huge_box_counts(self):
        p=power_charts([0,'-1/2','1/2'],2,[[-10**30,10**30]]*2,factors=[[2,2]])
        self.assertGreater(chart_population(p)['count'],10**59)
        for i in [0,10,10**30]:self.assertEqual(chart_rank(p,chart_select(p,i)),i)


class BranchingTests(unittest.TestCase):
    def test_all_signed_zeros_and_chart_identities(self):
        cases=[[[1,1,1]],[[1,0,2],[-1,3,0]],[[1,2,0],[1,0,2],[-1,0,0]],
               [[1,1,0],[-1,0,2]],[[4,2,0],[4,0,2],[-8,0,0]],[[2,0,0]]]
        for H in cases:
            p=branching_patch(H,[[-8,8],[-7,9]],2,3)
            self.assertTrue(verify_branching_patch(p))
            expected=[[x,y] for x in range(-8,9) for y in range(-7,10) if evaluate(H,x,y)==0]
            self.assertEqual(patch_scan(p)['points'],expected)
            for node in p['nodes']:
                a,b=node['source_residue'];m=node['step'];c=node['content']
                for u,v in [(-3,2),(0,0),(2,-4)]:
                    self.assertEqual(evaluate(H,a+m*u,b+m*v),c*evaluate(node['terms'],u,v))

    def test_genuine_singular_to_smooth_switching(self):
        p=branching_patch([[1,1,1]],[[-8,8]]*2,2,3)
        self.assertGreater(p['chart_switch_count'],0)
        kinds={b['chart'] for n in p['nodes'] if n['previous_chart']=='singular' for b in n['branches'] if b['switched']}
        self.assertEqual(kinds,{'vertical','horizontal'})
        self.assertEqual(len(patch_scan(p)['points']),33)

    def test_different_primes_and_depth(self):
        H=[[1,0,2],[-1,3,0]];b=[[-6,6]]*2
        for p in [2,3,5,7]:
            for e in [1,2]:
                q=branching_patch(H,b,p,e)
                expected=[[x,y] for x in range(-6,7) for y in range(-6,7) if y*y==x*x*x]
                self.assertEqual(patch_scan(q)['points'],expected)

    def test_disjoint_cells_rank_select(self):
        p=branching_patch([[1,1,1]],[[-7,10],[-9,12]],2,3)
        points=[patch_select(p,i) for i in range(p['candidate_count'])]
        self.assertEqual(len(points),len(set(map(tuple,points))))
        for i,z in enumerate(points):self.assertEqual(patch_rank(p,z),i)
        with self.assertRaises(IndexError):patch_select(p,len(points))

    def test_obstruction_budget_and_literal_tamper(self):
        p=branching_patch([[2,0,0]],[[-10**30,10**30]]*2,2,3)
        self.assertEqual(p['candidate_count'],0)
        self.assertEqual(patch_scan(p)['points'],[])
        with self.assertRaises(ValueError):branching_patch([[1,1,1]],[[-8,8]]*2,2,3,work_limit=1)
        q=copy.deepcopy(p);q['nodes'][0]['content']=2;self.assertFalse(verify_branching_patch(q))
        q=copy.deepcopy(p);q['complete_source_cover']=1;self.assertFalse(verify_branching_patch(q))


class WeightedTests(unittest.TestCase):
    def test_random_cauchy_binet(self):
        rng=random.Random(91827)
        for n in range(1,5):
            for h in range(1,7):
                for _ in range(3):
                    C=[[rng.randrange(-3,4) for j in range(h)] for i in range(n)]
                    V=[[rng.randrange(-3,4) for i in range(n)] for j in range(h)]
                    p=weighted_determinant(C,V,[rng.randrange(4) for j in range(h)],rng.choice([2,3,-2]))
                    self.assertEqual(p['unordered_sum'],p['determinant'])
                    self.assertEqual(p['determinant']%p['guaranteed_divisor'],0)
                    self.assertTrue(verify_weighted_determinant(p))

    def test_zero_minor_weight_improves_divisor(self):
        p=weighted_determinant([[0,1,0],[0,0,1]],[[1,1],[1,0],[0,1]],[0,2,3],2)
        self.assertEqual(p['minimum_active_weight'],5)
        self.assertEqual(p['guaranteed_divisor'],32)
        self.assertEqual(p['determinant'],32)

    def test_structural_zero_and_order_invariance(self):
        C=[[1,2,3],[2,4,6]];V=[[1,0],[0,1],[1,1]];w=[0,2,1]
        p=weighted_determinant(C,V,w,3)
        self.assertTrue(p['structural_zero']);self.assertEqual(p['determinant'],0)
        q=weighted_determinant([r[::-1] for r in C],V[::-1],w[::-1],3)
        self.assertEqual(q['determinant'],p['determinant'])

    def test_chart_derives_weights_and_relation(self):
        p=branching_patch([[1,1,1]],[[-16,16]]*2,2,3)
        i=next(i for i in p['leaf_ids'] if p['nodes'][i]['source_residue']==[0,0])
        q=chart_determinant(p,i,[[0,0],[8,0],[0,8]],[[0,0],[1,0],[0,1]])
        self.assertEqual(q['weighted_certificate']['determinant'],64)
        self.assertEqual(q['weighted_certificate']['guaranteed_divisor'],64)
        self.assertTrue(verify_chart_determinant(p,q))
        r=chart_determinant(p,i,[[0,0],[8,0],[16,0]],[[0,0],[1,0],[0,1]])
        self.assertEqual(r['weighted_certificate']['determinant'],0)
        self.assertIsNotNone(r['auxiliary'])
        with self.assertRaises(ValueError):chart_determinant(p,i,[[0,0],[8,0],[8,8]],[[0,0],[1,0],[0,1]])

    def test_literal_tampering(self):
        p=weighted_determinant([[1,2],[3,4]],[[1,0],[0,1]],[0,1],2)
        q=copy.deepcopy(p);q['subsets'][0]['term']+=1;self.assertFalse(verify_weighted_determinant(q))
        q=copy.deepcopy(p);q['structural_zero']=0;self.assertFalse(verify_weighted_determinant(q))
        with self.assertRaises(ValueError):weighted_determinant([[1]],[[1]],[True],2)

if __name__=='__main__':unittest.main()
