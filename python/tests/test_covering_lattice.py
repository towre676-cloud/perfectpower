import random
import unittest
from fractions import Fraction as Q
from math import gcd, isqrt
from perfectpower.covering import (FISHER_QUARTICS,evaluate,invariants,hessian,
    fisher_gamma,fisher_571_replay,hilbert,hensel_simple,two_isogeny_cover,
    covering_point,two_isogeny_point)
from perfectpower.integral_lattice import (smith_invariants,lattice_membership,
    inverse_lattice_conditions,basis_pullback,MinorLimit,local_torsion_profile)
from perfectpower.decomposition import compose,supplied_decomposition


def primes_of(n):
    n=abs(n);out=[];p=2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0:n//=p
        p+=1
    if n>1:out.append(n)
    return out


class CoveringTests(unittest.TestCase):
    def test_fisher_primary_source_replay(self):
        r=fisher_571_replay()
        self.assertEqual(r['invariants'],['44608','18842960','-2338816'])
        self.assertEqual(r['gamma'],['20/9','-64/9','-16/3'])
        self.assertEqual(r['finite_product'],-1)
        self.assertEqual([z['symbol'] for z in r['local_checks']],[1]*6+[-1])
        self.assertFalse(r['lean_certified'])
        self.assertEqual(len(r['global_dependencies']),3)

    def test_fisher_rejects_mutated_square_and_invariants(self):
        g1,g2,g3=FISHER_QUARTICS
        with self.assertRaises(ValueError):fisher_gamma(g1,g2,g3,(0,0,1))
        with self.assertRaises(ValueError):fisher_gamma(g1,g2,(1,2,3,4,5),(1,))
        with self.assertRaises(ValueError):invariants((1,2))

    def test_quartic_invariants_scale_under_square_rescaling(self):
        for g in FISHER_QUARTICS:
            I,J,D=invariants(g)
            for s in (-3,-1,2):
                self.assertEqual(invariants([s*s*c for c in g]),(s**4*I,s**6*J,s**12*D))
        self.assertEqual(evaluate(FISHER_QUARTICS[0],15,4),101)

    def test_hilbert_reciprocity_symmetry_bilinearity_square_invariance(self):
        rng=random.Random(711)
        for _ in range(150):
            a,b,c=[Q(rng.choice([i for i in range(-40,41) if i]),rng.randrange(1,20)) for j in range(3)]
            places=set([2]+primes_of(a.numerator*a.denominator*b.numerator*b.denominator))
            product=hilbert(a,b,'infinity')
            for p in places:product*=hilbert(a,b,p)
            self.assertEqual(product,1)
            for p in [2,3,5,7,11,'infinity']:
                self.assertEqual(hilbert(a,b,p),hilbert(b,a,p))
                self.assertEqual(hilbert(a,b*c,p),hilbert(a,b,p)*hilbert(a,c,p))
                self.assertEqual(hilbert(a*Q(49,16),b,p),hilbert(a,b,p))
                self.assertEqual(hilbert(a,-a,p),1)
        for place in (0,1,4,9,'real'):
            with self.assertRaises(ValueError):hilbert(1,1,place)
        with self.assertRaises(ValueError):hilbert(0,1,2)

    def test_hilbert_against_finite_norm_equation(self):
        # Unit/valuation representatives, primitive p-adic norm equations.
        for p in (3,5,7):
            for a in range(1,2*p):
                if a%p==0:continue
                for b in range(1,p):
                    for aa,bb in ((a,b),(a*p,b),(a,b*p)):
                        # Check x²-aa*y²=bb over finite residues independently.
                        norm_terms={(aa*y*y)%(p**3) for y in range(p**3)}
                        exists=any((x*x-bb)%(p**3) in norm_terms for x in range(p**3))
                        self.assertEqual(exists,hilbert(aa,bb,p)==1)

    def test_hensel_lifts_and_rejects_singular_seed(self):
        for p,seed in ((3,1),(5,1),(7,1)):
            r=hensel_simple((-1,0,1),p,seed,8)
            self.assertEqual(r['residual'],0)
            self.assertEqual(r['root'],1)
        with self.assertRaises(ValueError):hensel_simple((0,0,1),2,0,4)
        with self.assertRaises(ValueError):hensel_simple((-2,0,1),3,0,4)
        self.assertEqual(hensel_simple((-16,-41,-13,17,-3),2,16,12)['root'],2416)

    def test_covering_and_isogeny_on_many_actual_points(self):
        checked=0
        for A in range(-4,5):
            for B in range(-8,9):
                if B==0 or A*A==4*B:continue
                for d in range(-8,9):
                    if d==0 or B%d:continue
                    g=two_isogeny_cover(A,B,d)
                    for u in range(-3,4):
                        value=evaluate(g,u,1)
                        if value<0 or value.denominator!=1:continue
                        w=isqrt(int(value))
                        if w*w!=value:continue
                        x,y=covering_point(A,B,d,u,w)
                        self.assertEqual(y*y,x**3+A*x*x+B*x)
                        if x:
                            X,Y=two_isogeny_point(A,B,x,y)
                            self.assertEqual(Y*Y,X**3-2*A*X*X+(A*A-4*B)*X)
                        checked+=1
        self.assertGreater(checked,100)
        with self.assertRaises(ValueError):covering_point(1,2,1,1,100)
        with self.assertRaises(ValueError):two_isogeny_cover(2,1,1)
        with self.assertRaises(ValueError):two_isogeny_cover(0,2,3)


class LatticeTests(unittest.TestCase):
    def test_prime_power_depth(self):
        r=smith_invariants([[19,0],[0,19**2]])
        self.assertEqual(r['smith_factors'],[19,361])
        self.assertEqual(r['torsion_order'],19**3)
        profile=local_torsion_profile([[19,0],[0,19**2]],19)
        self.assertEqual(profile['torsion_lengths'],[1,2])
        self.assertEqual(profile['rank_mod_prime'],0)
        self.assertEqual(profile['torsion_length_sum'],3)
        r=basis_pullback([[19,0],[0,361]],[19,19])
        self.assertFalse(r['member'])
        self.assertEqual(r['obstructions'][0]['modulus'],361)
        self.assertEqual(r['obstructions'][0]['residue'],19)

    def test_unimodular_invariance_with_huge_coefficients(self):
        M=[[2,0,0],[0,6,0],[0,0,30]]
        want=smith_invariants(M)['smith_factors']
        for i in range(3):
            for j in range(3):
                if i==j:continue
                N=[row[:] for row in M]
                N[i]=[x+10**120*y for x,y in zip(N[i],N[j])]
                self.assertEqual(smith_invariants(N)['smith_factors'],want)
                N=[row[:] for row in M]
                for row in N:row[i]+=10**120*row[j]
                self.assertEqual(smith_invariants(N)['smith_factors'],want)

    def test_rectangular_lattice_membership_and_free_rank(self):
        a=[[2,0,4],[0,3,6],[0,0,0]]
        self.assertEqual(smith_invariants(a)['free_rank'],1)
        for b,want in [([2,3,0],True),([1,3,0],False),([2,3,1],False)]:
            self.assertEqual(lattice_membership(a,b)['member'],want)
        self.assertTrue(lattice_membership([[0],[0]],[0,0])['member'])
        self.assertFalse(lattice_membership([[0],[0]],[0,1])['member'])

    def test_basis_membership_vs_independent_augmented_minors(self):
        rng=random.Random(412)
        for _ in range(100):
            A=[[rng.randrange(-6,7) for j in range(3)] for i in range(3)]
            if smith_invariants(A)['rank']!=3:continue
            for b in ([rng.randrange(-8,9) for i in range(3)],
                      [sum(row[j]*j for j in range(3)) for row in A]):
                direct=basis_pullback(A,b)
                self.assertEqual(direct['member'],lattice_membership(A,b)['member'])
                if direct['member']:
                    self.assertEqual([sum(row[j]*direct['coordinates'][j] for j in range(3)) for row in A],b)

    def test_existing_order_maps_and_orbit_image_filter(self):
        import json
        from pathlib import Path
        from orbit_lattice import order_image_allowed
        maps=json.loads((Path(__file__).resolve().parents[2]/'receipts/order_transports.json').read_text())['embeddings']
        for e in maps:
            self.assertEqual(smith_invariants(e['matrix'])['torsion_order'],e['index'])
            for j in range(3):
                b=[row[j] for row in e['matrix']]
                self.assertEqual(basis_pullback(e['matrix'],b)['coordinates'],[int(i==j) for i in range(3)])
        M=[[3,0,0],[0,1,0],[0,0,1]]
        bad=order_image_allowed(M,9,6,[(1,0,0)],(1,0,0),2,1)
        good=order_image_allowed(M,9,6,[(1,0,0)],(3,0,0),2,1)
        self.assertEqual(bad['modulus'],6)
        self.assertEqual(bad['allowed_residues'],[])
        self.assertEqual(good['allowed_residues'],[[0]])
        self.assertFalse(bad['global_exponent_bound'])

    def test_budget_and_noninteger_presentations_rejected(self):
        with self.assertRaises(MinorLimit):smith_invariants([[1,0],[0,1]],minor_limit=1)
        with self.assertRaises(ValueError):smith_invariants([[Q(1,2)]])
        with self.assertRaises(ValueError):inverse_lattice_conditions([[0]])
        with self.assertRaises(ValueError):basis_pullback([[1]],[Q(1,2)])


class DecompositionTests(unittest.TestCase):
    def test_no_invalid_outer_cancellation(self):
        outer=(0,0,1);F=(0,1);G=(0,-1)
        r=supplied_decomposition(compose(outer,F),compose(outer,G),outer,F,G)
        self.assertFalse(r['equivalence_to_inner_equality'])
        self.assertEqual(r['status'],'FORWARD_ONLY')
        self.assertEqual(compose(outer,F),compose(outer,G))
        self.assertNotEqual(F,G)

    def test_affine_outer_and_false_certificate(self):
        outer=(3,-2);F=(1,2,3);G=(-1,0,1)
        r=supplied_decomposition(compose(outer,F),compose(outer,G),outer,F,G)
        self.assertTrue(r['equivalence_to_inner_equality'])
        with self.assertRaises(ValueError):supplied_decomposition((1,),compose(outer,G),outer,F,G)


if __name__=='__main__':unittest.main()
