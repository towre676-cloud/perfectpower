import unittest
from fractions import Fraction as Q
from perfectpower import polyalg as P
from perfectpower.power_free_local import bezout_certificate,root_lifts,local_admissibility,power_free_wheel,native_certificate
from perfectpower.divisor_square import WorkLimit


class PowerFreeLocalTests(unittest.TestCase):
    def test_bezout_nonmonic_and_signed(self):
        for f in ([1,0,0,0,1],[4,0,0,0,1],[-3,0,2],[-1,1],[3,-3,0,1],[-1,0,0,0,-1]):
            b=bezout_certificate(f)
            self.assertEqual(P.add(P.mul(P.poly(b['u']),P.poly(f)),P.mul(P.poly(b['v']),P.derivative(P.poly(f)))),P.poly([b['constant']]))
            self.assertGreater(b['constant'],0)

    def test_full_lifts_match_bruteforce(self):
        for f in ([1,0,0,0,1],[4,0,0,0,1],[0,-1,0,0,1],[0,0,1],[0,2],[0,1]):
            for prime in (2,3,5,7):
                for k in (1,2,3):
                    row=root_lifts(f,prime,k)
                    for level in row['levels']:
                        q=level['modulus']
                        self.assertEqual(level['roots'],[x for x in range(q) if P.evaluate(f,x)%q==0])

    def test_singular_roots_branch_and_die(self):
        row=root_lifts([4,0,0,0,1],2,3)
        self.assertEqual([r['roots'] for r in row['levels']],[[0],[0,2],[]])
        self.assertEqual(root_lifts([1,0,1],2,2)['roots'],[])

    def test_admissibility_includes_reducible_and_content(self):
        for f in ([1,0,0,0,1],[4,0,0,0,1],[-1,1],[-1,0,0,0,-1]):
            self.assertTrue(local_admissibility(f)['locally_admissible'])
        bad=local_admissibility([4,0,0,0,4])
        self.assertFalse(bad['locally_admissible']);self.assertEqual(bad['fixed_divisor_prime'],2)
        for x in range(-20,21):self.assertEqual(P.evaluate(bad['coefficients'],x)%4,0)
        self.assertFalse(local_admissibility([0,1,1],1)['locally_admissible'])

    def test_no_repeated_root_admissibility_claim(self):
        with self.assertRaises(ValueError):local_admissibility([0,0,1])
        self.assertEqual(root_lifts([0,0,1],3,2)['roots'],[0,3,6])

    def test_omitted_primes_obey_degree_bound(self):
        for f in ([1,0,0,0,1],[-3,0,2],[3,-3,0,1],[4,0,0,0,1]):
            p=local_admissibility(f)
            for prime in (2,3,5,7,11,13,17,19,23,29,31):
                row=root_lifts(f,prime,2)
                if prime not in p['exceptional_primes']:
                    self.assertLessEqual(row['rho'],p['degree'])
                    self.assertLess(row['rho'],prime**2)

    def test_wheel_matches_signed_interval(self):
        for f in ([1,0,0,0,1],[4,0,0,0,1],[0,-1,0,0,1],[-3,0,2]):
            w=power_free_wheel(f,primes=[5,2,3,2],lo=-127,hi=163)
            accepted=set(w['allowed']);expected=[x for x in range(-127,164) if all(P.evaluate(f,x)%(p*p) for p in (2,3,5))]
            self.assertEqual(w['count'],len(expected))
            self.assertEqual([x for x in range(-127,164) if x%w['modulus'] in accepted],expected)
            self.assertEqual(Q(w['density']),Q(len(accepted),w['modulus']))
            huge=power_free_wheel(f,lo=-10**30,hi=10**30)
            self.assertGreater(huge['count'],10**29)

    def test_wheel_global_obstruction(self):
        w=power_free_wheel([4,0,0,0,4],lo=-100,hi=100)
        self.assertTrue(w['global_obstruction']);self.assertEqual(w['count'],0)
        self.assertFalse(power_free_wheel([1,0,0,0,1])['global_obstruction'])

    def test_native_source_binds_claim(self):
        good=native_certificate([1,0,0,0,1]);bad=native_certificate([4,0,0,0,4])
        self.assertIn('LocallyAdmissible source 2',good['lean']['source'])
        self.assertIn('¬ PowerFree 2',bad['lean']['source'])
        self.assertFalse(good['lean']['kernel_checked'])
        self.assertIn('roots_2_complete',good['lean']['source'])
        self.assertNotIn('native_decide',good['lean']['source'])

    def test_bad_inputs_and_explicit_stops(self):
        for f in ([],[1],[0],[True,1],[Q(1,2),1]):
            with self.assertRaises(ValueError):local_admissibility(f)
        for k in (0,True,65):
            with self.assertRaises(ValueError):local_admissibility([1,1],k)
        with self.assertRaises(WorkLimit):local_admissibility([1,0,0,0,1],modulus_limit=3)
        with self.assertRaises(WorkLimit):root_lifts([0,0,1],7,3,work_limit=2)
        with self.assertRaises(WorkLimit):power_free_wheel([1,1],period_limit=8)
        with self.assertRaises(ValueError):root_lifts([1,1],4,2)
        with self.assertRaises(ValueError):power_free_wheel([1,1],lo=1,hi=0)

    def test_service_operations(self):
        from perfectpower.catalogue import Catalogue
        from perfectpower.query_service import dispatch
        c=None
        r=dispatch(c,{'op':'power_free_local','args':{'coefficients':[1,0,0,0,1]}})
        self.assertTrue(r['locally_admissible'])
        self.assertEqual(dispatch(c,{'op':'power_free_wheel','args':{'coefficients':[4,0,0,0,4],'lo':-50,'hi':50}})['count'],0)
        self.assertIn('lean',dispatch(c,{'op':'native_power_free_certificate','args':{'coefficients':[1,1]}}))
