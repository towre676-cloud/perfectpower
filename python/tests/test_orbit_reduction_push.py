import copy
import os
from math import isqrt
import random
import unittest
from perfectpower.checked_pell_orbits import pell_orbits_certificate,check_pell_orbits
from perfectpower.automatic_population import automatic_population_certificate,check_automatic_population,power_plus_constant,_power
from perfectpower.divisor_square import WorkLimit
from perfectpower.query_service import dispatch
from perfectpower.catalogue import Catalogue


def scan_norm(D,N,cap,domain='integer'):
    out=[]
    for x in range(-cap,cap+1):
        v=D*x*x+N
        if v<0:continue
        y=isqrt(v)
        if y*y!=v:continue
        for z in sorted({-y,y}):
            if domain=='integer' or (x>=0 and z>=0 if domain=='nonnegative' else x>0 and z>0):out.append([x,z])
    return out


class OrbitReductionTests(unittest.TestCase):
    def test_generalized_orbits_against_independent_scan(self):
        for D in (2,3,5,6,7,8,10,11,12):
            for N in range(-16,17):
                p=pell_orbits_certificate(D,N,50,work_limit=65536)
                self.assertEqual(p['source_points'],scan_norm(D,N,50),(D,N))
        for domain in ('integer','nonnegative','positive'):
            self.assertEqual(pell_orbits_certificate(3,-3,100,domain=domain)['source_points'],scan_norm(3,-3,100,domain))

    def test_two_orbits_and_fast_selection(self):
        p=pell_orbits_certificate(2,7,100,global_ranks=[{'orbit':0,'rank':1000},{'orbit':1,'rank':1000}])
        self.assertEqual(p['seeds'],[[3,1],[5,3]])
        self.assertEqual(p['source_count'],20)
        for s in p['global_selections']:
            x,y=s['point'];self.assertEqual(y*y-2*x*x,7)
        self.assertNotEqual(p['global_selections'][0]['point'],p['global_selections'][1]['point'])

    def test_automatic_recognition_and_original_coordinates(self):
        rng=random.Random(818)
        for e in (2,3):
            for _ in range(20):
                u=[rng.randrange(-3,4),rng.randrange(-3,4),rng.choice((-2,-1,1,2))]
                k=15 if e==2 else -2
                cs=_power(u,e);cs[0]+=k
                self.assertEqual(power_plus_constant(cs,e)[1],k)
                p=automatic_population_certificate(cs)
                expected=[]
                for x in range(-100,101):
                    v=sum(c*x**i for i,c in enumerate(cs))
                    if v<0:continue
                    y=isqrt(v)
                    if y*y==v:expected.extend([[x,z] for z in sorted({-y,y})])
                self.assertEqual(p['source_points'],expected)
        for a in range(1,7):
            for b in (-3,0,1,4):
                for c in (-2,1,3):
                    if isqrt(a)**2==a and b*b==4*a*c:continue
                    cs=[c,b,a]
                    p=automatic_population_certificate(cs,cutoff=50,work_limit=65536)
                    expected=[]
                    for x in range(-50,51):
                        v=a*x*x+b*x+c
                        if v<0:continue
                        y=isqrt(v)
                        if y*y==v:expected.extend([[x,z] for z in sorted({-y,y})])
                    self.assertEqual(p['source_points'],expected,cs)

    def test_limits_and_no_silent_fallback(self):
        with self.assertRaises(WorkLimit):pell_orbits_certificate(13,7,100,work_limit=4096)
        with self.assertRaises(ValueError):automatic_population_certificate([1,1,2])
        with self.assertRaises(ValueError):automatic_population_certificate([1,1,1,1,1])
        with self.assertRaises(ValueError):pell_orbits_certificate(4,1,100)
        with self.assertRaises(ValueError):pell_orbits_certificate(2,7,100,global_ranks=[{'orbit':9,'rank':0}])
        p=pell_orbits_certificate(2,7,100);bad=copy.deepcopy(p);bad['source_points'].pop()
        self.assertFalse(check_pell_orbits(bad)['accepted'])
        p=automatic_population_certificate([15,0,1]);bad=copy.deepcopy(p);bad['reduction']['offset']=17
        self.assertFalse(check_automatic_population(bad)['accepted'])

    def test_dispatch(self):
        c=Catalogue(':memory:')
        self.assertEqual(dispatch(c,dict(op='checked_pell_orbits',args=dict(D=2,norm=7,cutoff=100)))['source_count'],20)
        self.assertEqual(dispatch(c,dict(op='checked_auto_population',args=dict(coefficients=[1,1,1])))['source_count'],4)

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_LEAN') and os.environ.get('LEAN_PATH'),'actual Lean toolchain required')
    def test_actual_kernel_routes(self):
        packets=[(pell_orbits_certificate(2,7,100,global_ranks=[{'orbit':1,'rank':1000}]),check_pell_orbits),
            (pell_orbits_certificate(3,-3,100,domain='positive'),check_pell_orbits),
            (pell_orbits_certificate(2,0,100),check_pell_orbits)]
        for cs,cap in [([15,0,1],None),([1,1,1],None),([1,1,2],10**12),([-2,0,0,1],None),([-13,0,0,1],None)]:
            packets.append((automatic_population_certificate(cs,cutoff=cap),check_automatic_population))
        for p,check in packets:
            result=check(p,timeout=240)
            self.assertTrue(result['accepted'],result)


if __name__=='__main__':unittest.main()
