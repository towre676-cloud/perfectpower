import itertools
import random
import unittest
from fractions import Fraction
from perfectpower.dresden import (long_count_days, days_long_count, Progression,
    calendar_round, calendar_phase, solve_alternatives, venus_rules, reconstruct_intervals, polynomial_calendar, polynomial_calendar_select)


class DresdenTests(unittest.TestCase):
    def test_long_count_roundtrip(self):
        for n in list(range(1500))+[10**30, 1366560]:
            for places in (1, 2, 3, 5, 8):
                self.assertEqual(long_count_days(days_long_count(n, places)), n)
        self.assertEqual(long_count_days([4,12,8,0]), 33280)
        self.assertEqual(long_count_days([1,5,14,4,0]), 185120)
        for bad in ([1,18,0], [1,-1], [True], []):
            with self.assertRaises(ValueError): long_count_days(bad)

    def test_crt_exhaustive(self):
        for m,n in itertools.product(range(1,13), repeat=2):
            for a,b in itertools.product(range(m),range(n)):
                p = Progression(a,m).intersect(Progression(b,n))
                hits = [x for x in range(-50,51) if x%m==a and x%n==b]
                self.assertEqual([] if p is None else [x for x in range(-50,51) if p.contains(x)], hits)
                if p:
                    self.assertEqual(p.count(-50,50), len(hits))
                    self.assertEqual([p.select(i,-50,50) for i in range(len(hits))], hits)

    def test_calendar_full_round(self):
        for n in range(18980):
            self.assertEqual(calendar_round(*calendar_phase(n)).residue, n)
        self.assertIsNone(calendar_round(1,19,0))
        with self.assertRaises(ValueError): calendar_round(0,0,0)

    def test_large_population(self):
        p=Progression(0,37960)
        hi=37960*10**30
        self.assertEqual(p.count(0,hi),10**30+1)
        self.assertEqual(p.select(10**30,0,hi),hi)
        with self.assertRaises(IndexError): p.select(-1,0,hi)

    def test_source_alternatives(self):
        def r(i,a,m): return dict(id=i,residue=a,modulus=m,source='synthetic',location='fixture')
        out=solve_alternatives([[r('a',0,4),r('b',1,4)],[r('c',0,6)]],-100,100)
        self.assertEqual(len(out['survivors']),1)
        self.assertEqual(out['survivors'][0]['modulus'],12)
        with self.assertRaises(ValueError): solve_alternatives([[r('a',0,4),r('b',1,4)]],0,10,combination_limit=1)

    def test_venus_envelopes(self):
        for rule in venus_rules():
            for ref in ('583.9214','584','585'):
                for n in (0,1,121,122,182,183,500):
                    e=[Fraction(rule.execute(i,reference=ref)['error_against_mean']) for i in range(n+1)]
                    packet=rule.error_envelope(n,reference=ref)
                    self.assertEqual(Fraction(packet['minimum']),min(e))
                    self.assertEqual(Fraction(packet['maximum']),max(e))
        self.assertEqual(venus_rules()[1].mean_period,venus_rules()[2].mean_period)
        self.assertEqual(venus_rules()[1].execute(122)['day'],71240)

    def test_polynomial_original_coordinates(self):
        for m in (1,3,260,10**30):
            p=Progression(2,m)
            pred={'poly':[-9,0,1],'relation':'>='}
            lo,hi=(-100,100) if m<1000 else (-10**32,10**32)
            packet=polynomial_calendar(p,pred,lo,hi)
            if m<1000:
                hits=[n for n in range(lo,hi+1) if p.contains(n) and n*n>=9]
                self.assertEqual(packet['count'],len(hits))
                self.assertEqual([polynomial_calendar_select(packet,i) for i in range(len(hits))],hits)
            else:
                self.assertEqual(packet['count'],p.count(lo,hi)-1)
            with self.assertRaises(IndexError): polynomial_calendar_select(packet,packet['count'])

    def test_reconstruction_against_exhaustion(self):
        rng=random.Random(42)
        for _ in range(100):
            opts=[sorted(set(rng.randrange(0,8) for _ in range(3))) for _ in range(5)]
            target=rng.randrange(0,35)
            hits=[x for x in itertools.product(*opts) if sum(x)==target]
            out=reconstruct_intervals(opts,target)
            self.assertEqual(out['count'],len(hits))
            self.assertEqual(out['viable_values'],[sorted({x[i] for x in hits}) for i in range(5)])
            if hits:self.assertIn(tuple(out['witness']),hits)
        with self.assertRaises(ValueError): reconstruct_intervals([[1,2]]*20,30,state_limit=2)

if __name__=='__main__': unittest.main()
