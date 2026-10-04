import itertools
import random
import unittest
from fractions import Fraction as Q
from math import factorial, gcd, prod
from perfectpower.divisor_kernel import (DivisorKernel,KernelLimit,divisor_transform,
    power_kernel,sigma_kernel,sparse_divisor_counts,sparse_pairing,threshold_solve)
from perfectpower.exact_linear import apply,rank
from perfectpower.integral_lattice import determinant
from perfectpower.integer_lifting import solve_integer


def dense(kernel):
    w=kernel.weights()
    return [[Q(w[gcd(i,j)-1],max(i,j)) if kernel.normalized else w[gcd(i,j)-1]
             for j in range(1,kernel.n+1)] for i in range(1,kernel.n+1)]


class DivisorKernelTests(unittest.TestCase):
    def test_four_transforms_against_direct_incidence(self):
        rng=random.Random(8102026)
        for n in range(1,40):
            x=[Q(rng.randrange(-7,8),rng.randrange(1,5)) for _ in range(n)]
            for multiples in (False,True):
                direct=[sum(x[j-1] for j in range(1,n+1) if (j%i==0 if multiples else i%j==0)) for i in range(1,n+1)]
                y=divisor_transform(x,multiples=multiples)
                self.assertEqual(y,direct)
                self.assertEqual(divisor_transform(y,inverse=True,multiples=multiples),x)

    def test_mobius_direction_and_jordan_coefficients(self):
        self.assertEqual(power_kernel(10).g,(1,1,2,2,4,2,6,4,6,4))
        self.assertEqual(power_kernel(5,2).g,(1,3,8,12,24))
        self.assertEqual(power_kernel(5,0).g,(1,0,0,0,0))
        self.assertEqual(DivisorKernel.from_weights([1,3,4,7,6,12]).g,(1,2,3,4,5,6))

    def test_random_signed_exact_actions_and_energy(self):
        rng=random.Random(20260108)
        for _ in range(60):
            n=rng.randrange(1,24);g=[Q(rng.randrange(-3,6),rng.randrange(1,4)) for _ in range(n)]
            x=[rng.randrange(-4,5) for _ in range(n)]
            for normalized in (False,True):
                k=DivisorKernel(g,normalized=normalized);a=dense(k);y=list(apply(a,x))
                self.assertEqual(k.apply(x),y)
                self.assertEqual(k.energy(x),sum(u*v for u,v in zip(x,y)))
                self.assertEqual(DivisorKernel.from_weights(k.weights(),normalized=normalized).g,k.g)

    def test_raw_rank_inertia_and_determinant(self):
        for g in ([1,-2,0,4],[0,0,0],[Q(1,3),2,-5],[1,0,0,0]):
            k=DivisorKernel(g);c=k.certificate();a=dense(k)
            self.assertEqual(c['rank'],rank(a));self.assertEqual(c['determinant'],determinant(a))
            self.assertEqual(c['determinant'],prod(g))
            self.assertEqual(c['inertia']['negative'],sum(v<0 for v in g))

    def test_positive_weights_can_have_negative_energy(self):
        k=DivisorKernel.from_weights([1,Q(1,10)],normalized=True)
        self.assertEqual(k.apply([1,-2]),[0,Q(2,5)])
        self.assertEqual(k.energy([1,-2]),Q(-4,5))
        self.assertEqual(k.certificate()['status'],'SIGNED_GRAM_INCONCLUSIVE')
        self.assertFalse(DivisorKernel.from_weights([1,Q(1,10)]).certificate()['positive_semidefinite'])

    def test_signed_normalized_coefficients_are_not_an_indefiniteness_test(self):
        # g[2]<0 yet this normalized 2x2 matrix is positive definite.
        k=DivisorKernel.from_weights([1,Q(3,4)],normalized=True)
        self.assertLess(k.g[1],0);self.assertGreater(determinant(dense(k)),0)
        self.assertEqual(k.certificate()['status'],'SIGNED_GRAM_INCONCLUSIVE')

    def test_constant_weight_has_different_raw_and_normalized_ranks(self):
        self.assertEqual(power_kernel(12,0).certificate()['rank'],1)
        c=power_kernel(12,0,normalized=True).certificate()
        self.assertEqual(c['rank'],12);self.assertTrue(c['positive_definite'])

    def test_nonnegative_threshold_gram_kernel_is_coordinate_supported(self):
        for g in ([0,1,0,0,0,0],[0,1,1,0,0,0],[0]*6,[1,0,0,0,0,0]):
            k=DivisorKernel(g,normalized=True);c=k.certificate()
            self.assertEqual(c['rank'],rank(dense(k)))
            for j in c['coordinate_kernel']:
                x=[int(i==j) for i in range(1,7)]
                self.assertEqual(k.apply(x),[0]*6)

    def test_constant_normalized_tridiagonal_inverse_and_determinant(self):
        for n in range(1,25):
            k=power_kernel(n,0,normalized=True)
            rhs=[Q((i*i%19)-9,3) for i in range(1,n+1)]
            self.assertEqual(k.apply(threshold_solve(rhs)),rhs)
            integer_rhs=[i**3-7 for i in range(1,n+1)]
            self.assertTrue(all(type(v) is int for v in threshold_solve(integer_rhs)))
            self.assertEqual(k.apply(threshold_solve(integer_rhs)),integer_rhs)
            if n<=7:self.assertEqual(determinant(dense(k)),Q(1,factorial(n)**2))

    def test_complete_rational_fibres_and_independent_integer_decisions(self):
        rng=random.Random(39912)
        for _ in range(75):
            n=rng.randrange(1,6);g=[rng.randrange(-3,4) for _ in range(n)]
            b=[rng.randrange(-4,5) for _ in range(n)];k=DivisorKernel(g)
            got=k.solve(b,domain='integer');reference=solve_integer(dense(k),b)
            self.assertEqual(got['status']=='COMPLETE_DIVISOR_AFFINE_FIBRE',reference['status']=='INTEGER_AFFINE_FIBRE')
            rational=k.solve(b)
            if rational['status']=='COMPLETE_DIVISOR_AFFINE_FIBRE':
                x=k.lift(rational,[Q(2,3)]*len(rational['free_divisor_coordinates']))
                self.assertEqual(k.apply(x),b)
            if got['status']=='COMPLETE_DIVISOR_AFFINE_FIBRE':
                self.assertEqual(k.apply(got['particular']),b)
                for x in itertools.product(range(-2,3),repeat=n):
                    if k.apply(x)!=b:continue
                    u=divisor_transform(x,multiples=True)
                    parameters=[u[j-1] for j in got['free_divisor_coordinates']]
                    self.assertEqual(k.lift(got,parameters),list(x))

    def test_image_and_divisibility_obstructions(self):
        k=DivisorKernel([1,0,0]);self.assertEqual(k.solve([1,2,1])['status'],'DIVISOR_IMAGE_OBSTRUCTION')
        k=DivisorKernel([1,2]);r=k.solve([0,1],domain='integer')
        self.assertEqual((r['status'],r['modulus'],r['residue']),('DIVISOR_CONGRUENCE_OBSTRUCTION',2,1))
        self.assertEqual(k.apply(k.solve([0,1])['particular']),[0,1])

    def test_sparse_corpus_pairings_against_pairwise_gcd(self):
        a=[1,6,12,15,15,36];b=[2,9,22,70];ca=sparse_divisor_counts(a);cb=sparse_divisor_counts(b)
        self.assertEqual(ca[1],6);self.assertEqual(ca[3],5)
        for degree in range(4):
            brute=sum(sum(d**degree for d in range(1,gcd(i,j)+1) if gcd(i,j)%d==0) for i in a for j in b)
            self.assertEqual(sparse_pairing(ca,cb,degree=degree),brute)

    def test_sigma_kernel_is_inverse_decodable(self):
        k=sigma_kernel(96);x=[(i*i%17)-8 for i in range(96)];y=k.apply(x)
        self.assertEqual(k.solve(y,domain='integer')['particular'],x)
        self.assertEqual(k.g,tuple(range(1,97)))

    def test_explicit_numerical_mode(self):
        k=sigma_kernel(40,normalized=True,exact=False);x=[((i*7)%19)-9 for i in range(40)]
        exact=sigma_kernel(40,normalized=True)
        for u,v in zip(k.apply(x),exact.apply(x)):self.assertAlmostEqual(u,float(v),places=10)
        self.assertAlmostEqual(k.energy(x),float(exact.energy(x)),places=9)
        self.assertEqual(k.certificate()['status'],'NUMERICAL_ONLY')

    def test_input_domains_and_budget_failure(self):
        for values in ([],[True],[1.2],['2']):
            with self.assertRaises(ValueError):DivisorKernel(values)
        with self.assertRaises(ValueError):DivisorKernel([float('nan')],exact=False)
        with self.assertRaises(KernelLimit):power_kernel(100,work_limit=10)
        with self.assertRaises(KernelLimit):DivisorKernel([1,2],size_limit=1)
        with self.assertRaises(ValueError):power_kernel(4,True)
        with self.assertRaises(ValueError):sigma_kernel(4,normalized=True).solve([0]*4)
        with self.assertRaises(ValueError):DivisorKernel([Q(1,2)]).solve([1],domain='integer')
        with self.assertRaises(ValueError):sparse_divisor_counts([0])
        with self.assertRaises(KernelLimit):sparse_divisor_counts([999983],work_limit=10)
        with self.assertRaises(ValueError):sigma_kernel(4).apply([1])


if __name__=='__main__':unittest.main()
