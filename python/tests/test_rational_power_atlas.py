import copy
from fractions import Fraction
import unittest
from perfectpower.rational_power_atlas import (power_atlas,verify_power_atlas,power_population,
    power_select,power_rank,power_scan,power_patch,verify_power_patch,native_power_atlas)
from perfectpower.residue_determinant import verify_auxiliary

class PowerAtlasTests(unittest.TestCase):
    def test_denominator_prime_not_cancelled_modulo_p(self):
        p=power_atlas(['0','1/2'],2,[[2,2]])
        self.assertTrue(verify_power_atlas(p));self.assertEqual(p['x_period'],8)
        # x=2 gives Q(x)=1, so y=0 is a false candidate of F-2*y^2 mod 2.
        self.assertEqual((2-2*0**2)%2,0)
        with self.assertRaises(ValueError):power_rank(p,[[0,8],[0,4]],[2,0])
        self.assertEqual(power_scan(p,[[-8,8],[-4,4]])['points'],[[0,0],[2,-1],[2,1],[8,-2],[8,2]])

    def test_integral_everywhere_keeps_all_charts(self):
        p=power_atlas(['0','-1/2','1/2'],2,[[2,3],[3,1]],explicit_limit=1)
        self.assertEqual([c['residue'] for c in p['charts']],[0,1])
        self.assertTrue(verify_power_atlas(p))
        b=[[-8,9],[-8,8]];points=[[x,y] for x in range(-8,10) for y in range(-8,9) if x*(x-1)==2*y*y]
        self.assertEqual(power_scan(p,b)['points'],points)

    def test_partial_domain_and_no_domain(self):
        p=power_atlas(['0','0','1/4'],2,[[3,1]])
        self.assertEqual([c['residue'] for c in p['charts']],[0,2])
        self.assertEqual(power_scan(p,[[-8,8],[-4,4]])['points'],[[x,y] for x in range(-8,9) for y in range(-4,5) if x*x==4*y*y])
        q=power_atlas(['1/2'],2,[[2,1]])
        self.assertTrue(verify_power_atlas(q));self.assertTrue(q['global_obstruction'])
        self.assertEqual(power_population(q,[[-100,100],[-100,100]])['count'],0)

    def test_signed_counts_and_rank_select(self):
        p=power_atlas(['0','1/2'],3,[[2,2],[3,1]],explicit_limit=1);b=[[-9,10],[-5,6]]
        # Original numerator relation must be tested at L*M=24, not M=12.
        expected=[[x,y] for x in range(-9,11) for y in range(-5,7) if (x-2*y**3)%24==0]
        count=power_population(p,b)['count'];self.assertEqual(count,len(expected))
        actual=[]
        for i in range(count):
            z=power_select(p,b,i);actual.append(z);self.assertEqual(power_rank(p,b,z),i)
        self.assertEqual(sorted(actual),expected)
        with self.assertRaises(IndexError):power_select(p,b,count)
        with self.assertRaises(IndexError):power_select(p,b,-1)

    def test_shared_prime_partial_domains(self):
        restrictions=[{'terms':[[1,1,0],[1,0,1]],'prime':2,'exponent':2}]
        p=power_atlas(['0','1/2'],2,[[2,3],[3,1]],restrictions=restrictions)
        self.assertTrue(verify_power_atlas(p));self.assertEqual(p['parameter_period'],24)
        b=[[-8,12],[-5,5]]
        expected=[[x,y] for x in range(-8,13) for y in range(-5,6) if x==2*y*y and (x+y)%4==0]
        self.assertEqual(power_scan(p,b)['points'],expected)
        candidates=[[x,y] for x in range(-8,13) for y in range(-5,6) if (x-2*y*y)%48==0 and (x+y)%4==0]
        self.assertEqual(power_population(p,b)['count'],len(candidates))

    def test_empty_parameter_charts_and_huge_bounds(self):
        p=power_atlas(['0','0','1/4'],2,[[2,2]])
        self.assertEqual(power_population(p,[[1,1],[0,0]])['count'],0)
        h=10**50;b=[[-h,h],[-h,h]];count=power_population(p,b)['count']
        self.assertGreater(count,10**98)
        for i in (0,count//2,count-1):self.assertEqual(power_rank(p,b,power_select(p,b,i)),i)

    def test_patch_all_orientations_and_auxiliaries(self):
        p=power_atlas(['0','0','0','1'],2,[[2,3],[3,2]])
        patch=power_patch(p,[[-5,5],[-5,5]])
        self.assertEqual(patch['scan']['points'],[[0,0],[1,-1],[1,1]])
        self.assertGreater(patch['lift_orientations']['singular'],0)
        self.assertGreater(patch['lift_orientations']['vertical'],0)
        self.assertGreater(patch['lift_orientations']['horizontal'],0)
        self.assertTrue(verify_auxiliary(patch['auxiliary']))
        self.assertTrue(verify_power_patch(patch))
        bad=copy.deepcopy(patch);bad['scan']['points'].pop();self.assertFalse(verify_power_patch(bad))
        bad=copy.deepcopy(patch);bad['lift_orientations']['singular']+=1;self.assertFalse(verify_power_patch(bad))

    def test_source_and_chart_corruption(self):
        p=power_atlas(['0','1/2'],2,[[2,2]])
        for key,value in [('x_period',4),('denominator',True),('complete_integer_domain',1),('unexpected',True),('global_obstruction',True)]:
            q=copy.deepcopy(p);q[key]=value;self.assertFalse(verify_power_atlas(q))
        for change in ('chart','source','cover'):
            q=copy.deepcopy(p)
            if change=='chart':q['charts'][0]['quotient_coefficients'][0]+=1
            elif change=='source':q['rational_coefficients'][1]='1/3'
            else:q['charts'][0]['cover']['locals'][0]['roots'].pop()
            self.assertFalse(verify_power_atlas(q))
        for q in ({},None,[]):self.assertFalse(verify_power_atlas(q))

    def test_query_and_native_bridge(self):
        from perfectpower.query_service import dispatch
        p=dispatch(None,{'op':'rational_power_atlas','args':{'coefficients':['0','1/2'],'exponent':2,'factors':[[2,2]]}})
        self.assertTrue(dispatch(None,{'op':'verify_rational_power_atlas','args':{'packet':p}})['valid'])
        source=native_power_atlas(p,[[-2,2],[-1,1]])
        self.assertIn('denominator_transport',source);self.assertIn('population_checked',source)
        self.assertNotIn('sorry',source)
        r=dispatch(None,{'op':'weighted_gram_determinant','args':{'matrix':[[1,0],[0,1],[1,1]],'weights':[2,3,5]}})
        self.assertEqual(r['determinant'],['31','0'])

    def test_extra_restriction_has_own_prime_power(self):
        a=power_atlas(['0','1/2'],2,[[2,1],[3,1]],restrictions=[{'terms':[[1,1,0],[1,0,1]],'prime':2,'exponent':2}])
        self.assertEqual(a['equation_period'],6);self.assertEqual(a['parameter_period'],12)
        expected=[[x,y] for x in range(-6,7) for y in range(-3,4) if (x-2*y*y)%12==0 and (x+y)%4==0]
        self.assertEqual(power_population(a,[[-6,6],[-3,3]])['count'],len(expected))

    def test_budgets_and_literals(self):
        for args in [(['1/33'],2,[[2,1]]),([0,1],True,[[2,1]]),([0,1],1,[[2,1]])]:
            with self.assertRaises(ValueError):power_atlas(*args)
        p=power_atlas([0,1],2,[[2,1]])
        with self.assertRaises(ValueError):power_scan(p,[[-10,10],[-10,10]],candidate_limit=1)
        with self.assertRaises(ValueError):power_population(p,[[-10,10],[-10,10]],work_limit=1)

if __name__=='__main__':unittest.main()
