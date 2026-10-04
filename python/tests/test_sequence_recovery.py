import random
import unittest
from fractions import Fraction as Q
from math import gcd
from perfectpower.modular_reconstruction import combine,reconstruct,reconstruct_system,berlekamp_massey
from perfectpower.recurrence import Recurrence,CycleLimit,filter_count,discover_prefix,from_generating_function
from perfectpower.primary_modules import (primary_cyclic_counts,subgroup_census,cyclic_phase,
                                        presentation_cyclic_counts)
from perfectpower.exact_operators import Weyl,hypergeometric_replay,quotient_projectors
from perfectpower.quotient_algebra import QuotientAlgebra
from perfectpower import polyalg as P
from perfectpower.core import mul


class ReconstructionTests(unittest.TestCase):
    def test_bounded_reconstruction_exhaustive_small_fractions(self):
        M=577
        for b in range(1,9):
            for a in range(-8,9):
                if gcd(a,b)!=1:continue
                residue=a*pow(b,-1,M)%M
                self.assertEqual(reconstruct(residue,M,8,8),Q(a,b))
        self.assertEqual(reconstruct(0,17,0,1),0)
        with self.assertRaises(ValueError):reconstruct(1,128,8,8)
        with self.assertRaises(ValueError):reconstruct(100,577,1,1)

    def test_crt_noncoprime_and_large_signed_fraction(self):
        self.assertEqual(combine([(2,6),(5,9)]),(14,18))
        with self.assertRaises(ValueError):combine([(2,6),(3,9)])
        value=Q(-413,37);primes=(1009,1013,1019)
        rs=[(value.numerator*pow(value.denominator,-1,p)%p,p) for p in primes]
        self.assertEqual(reconstruct_system(rs,500,50)['value'],str(value))
        with self.assertRaises(ValueError):reconstruct_system(rs,10**9,10**9)

    def test_modular_bm_vs_known_random_recurrences(self):
        rng=random.Random(814)
        for r in range(1,7):
            for _ in range(20):
                cs=[rng.randrange(-5,6) for i in range(r)]
                if not cs[0]:cs[0]=1
                seq=Recurrence(tuple(cs),tuple(rng.randrange(-9,10) for i in range(r)))
                terms=list(map(int,seq.terms(5*r+10)));p=1013
                guess=berlekamp_massey(terms[:3*r+5],p)
                if guess:
                    for n in range(len(terms)-len(guess)):
                        self.assertEqual((terms[n+len(guess)]-sum(c*terms[n+i] for i,c in enumerate(guess)))%p,0)
        with self.assertRaises(ValueError):berlekamp_massey([1,2,3],15)


class RecurrenceTests(unittest.TestCase):
    def test_fast_signed_values_vs_independent_iteration(self):
        rng=random.Random(309)
        for r in range(1,6):
            for _ in range(10):
                cs=[rng.randrange(-3,4) for i in range(r)];cs[0]=rng.choice((-1,1))
                init=[rng.randrange(-6,7) for i in range(r)]
                rec=Recurrence(tuple(cs),tuple(init));a=dict(enumerate(init))
                for n in range(60):a[n+r]=sum(cs[i]*a[n+i] for i in range(r))
                for n in range(-1,-31,-1):a[n]=(a[n+r]-sum(cs[i]*a[n+i] for i in range(1,r)))//cs[0]
                for n in range(-30,60):self.assertEqual(rec.nth(n),a[n])
        with self.assertRaises(ValueError):Recurrence((0,1),(1,2)).nth(-1)
        with self.assertRaises(ValueError):Recurrence((0.5,),(1,))

    def test_generating_functions_multiply_back(self):
        for rec in (Recurrence((1,1,0),(1,1,1)),Recurrence((1,2),(0,1)),
                    Recurrence((0,0),(2,3)),Recurrence((Q(1,2),Q(1,3)),(1,2))):
            numerator,denominator=rec.generating_function();series=rec.terms(40)
            for n in range(40):
                coefficient=sum(q*series[n-i] for i,q in enumerate(denominator) if i<=n)
                self.assertEqual(coefficient,numerator[n] if n<len(numerator) else 0)

    def test_supplied_general_generating_function_bridge(self):
        for numerator,denominator in [((1,1),(1,0,-1,-1)),((0,0,0,7),(1,-2)),
                                      ((1,2,3),(2,)),((Q(1,3),),(1,Q(-1,2)))]:
            rec=from_generating_function(numerator,denominator)
            num,den=rec.generating_function()
            self.assertEqual(P.poly(mul(num,denominator)),P.poly(mul(numerator,den)))
        with self.assertRaises(ValueError):from_generating_function((1,),(0,1))

    def test_period_and_preperiod_counts_vs_direct_modular_iteration(self):
        for rec in (Recurrence((1,1,0),(1,1,1)),Recurrence((2,),(1,)),Recurrence((0,),(1,))):
            for m in (4,7,9):
                cert=rec.residue_filter(m,lambda s:s[0]==0)
                xs=rec.terms(250)
                for stop in range(251):
                    self.assertEqual(filter_count(cert,stop),sum(int(x)%m==0 for x in xs[:stop]))
        p=Recurrence((1,1,0),(1,1,1));c=p.residue_filter(7,lambda s:s[0]==0)
        self.assertEqual(c['period'],48)
        self.assertEqual(filter_count(c,10**12),250000000000)
        self.assertEqual(Recurrence((2,),(1,)).cycle(8)['preperiod'],3)
        with self.assertRaises(CycleLimit):p.cycle(7,state_limit=3)
        bad=c.copy();bad['cycle_hits']=[0,0]
        with self.assertRaises(ValueError):filter_count(bad,100)

    def test_discovery_and_mutation_never_promote_definition(self):
        seq=list(map(int,Recurrence((1,2),(0,1)).terms(40)))
        r=discover_prefix(seq)
        self.assertEqual(r['coefficients'],['1','2'])
        self.assertFalse(r['definition_proved'])
        seq[-1]+=1
        with self.assertRaises(ValueError):discover_prefix(seq)
        with self.assertRaises(ValueError):discover_prefix([1,2,3])
        with self.assertRaises(ValueError):discover_prefix(list(range(40)),heldout_primes=(1009,))


class PrimaryModuleTests(unittest.TestCase):
    def test_recovered_full_censuses(self):
        for p,exponents,want,cyclics in [(2,(3,2,1),81,27),(2,(2,2,2),129,35),(3,(2,2),23,16)]:
            r=subgroup_census(p,exponents)
            self.assertEqual(r['all_subgroups'],want)
            self.assertEqual(r['nontrivial_cyclic_subgroups'],cyclics)
            self.assertEqual(sum(r['subgroups_by_order'].values()),want)
        with self.assertRaises(ValueError):subgroup_census(2,(10,),element_limit=10)
        with self.assertRaises(ValueError):subgroup_census(2,(2,2),join_limit=1)

    def test_phase_keys_invariant_under_units_but_not_shadow(self):
        for p,es in [(2,(3,2,1)),(3,(2,2))]:
            rng=random.Random(71)
            for _ in range(40):
                g=tuple(rng.randrange(p**e) for e in es);r=cyclic_phase(p,es,g)
                for u in range(1,p**max(es)):
                    if u%p:
                        self.assertEqual(cyclic_phase(p,es,tuple(u*x for x in g)),r)
        first=cyclic_phase(2,(2,2),(1,1));second=cyclic_phase(2,(2,2),(1,3))
        self.assertEqual(first['coordinate_heights'],second['coordinate_heights'])
        self.assertNotEqual(first['canonical_generator'],second['canonical_generator'])
        self.assertEqual(presentation_cyclic_counts([[19,0],[0,361]],19)['exponents'],[1,2])
        with self.assertRaises(ValueError):presentation_cyclic_counts([[0]],2)


class OperatorTests(unittest.TestCase):
    def test_weyl_commutator_associativity_and_series_composition(self):
        t=Weyl({(1,0):1});D=Weyl({(0,1):1})
        self.assertEqual(D*t-t*D,1)
        A=(D+t)**2;B=t*D+3;C=D*D-t
        self.assertEqual((A*B)*C,A*(B*C))
        series=[Q(i*i+1) for i in range(40)]
        lhs=(A*B).act_series(series,20)
        rhs=A.act_series(B.act_series(series,30),20)
        self.assertEqual(lhs,rhs)
        with self.assertRaises(ValueError):D.act_series([1],1)
        with self.assertRaises(ValueError):Weyl({(0,-1):1})

    def test_recovered_hypergeometric_prefix(self):
        r=hypergeometric_replay(40)
        self.assertTrue(all(x=='0' for x in r['residuals']))
        self.assertEqual(r['series_prefix'][:3],['1','16/3','1024/105'])
        self.assertFalse(r['zeta_identity_proved'])

    def test_wilson_and_primary_projectors(self):
        r=quotient_projectors((0,11,0,1),[(0,1),(11,0,1)])
        self.assertEqual(r['projectors'],[['1','0','1/11'],['0','0','-1/11']])
        f=(1,-2,1);g=(1,1);mod=mul(f,g)
        r=quotient_projectors(mod,[f,g]);algebra=QuotientAlgebra(mod)
        es=[algebra.element(tuple(map(Q,row))) for row in r['projectors']]
        self.assertEqual(es[0]*es[1],algebra.element(0))
        self.assertEqual(es[0]+es[1],algebra.element(1))
        with self.assertRaises(ZeroDivisionError):quotient_projectors((1,-2,1),[(-1,1),(-1,1)])
        with self.assertRaises(ValueError):quotient_projectors((0,1),[(1,1)])


if __name__=='__main__':unittest.main()
