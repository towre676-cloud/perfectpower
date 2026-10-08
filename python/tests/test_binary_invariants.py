import random
import unittest
from fractions import Fraction as Q
from perfectpower.binary_invariants import (form, symmetric_tensor, transvectant,
    binary_substitute, quartic_invariants, quartic_covariants, contraction_invariants,
    compile_contractions,cubic_discriminant)
from perfectpower.quartic_cover_reduction import (reduce_cover, reduced_projective_lift,
    search_reduced_box, projective_residue_mask)
from perfectpower.mordell_cover_charts import chart_cover

C=dict(quartic=['-2','0','0','1'],x_numerator=['0','-2','0','0','1'],
       y_numerator=['4','0','0','-4','0','0','1'])


class InvariantContractions(unittest.TestCase):
    def test_reusable_contraction_program_and_cubic(self):
        f=[1,2,3,4,5]
        packet=compile_contractions([dict(degree=4,coefficients=f)],
            [dict(left=0,right=0,contractions=2),
             dict(left=0,right=0,contractions=4,scale=6),
             dict(left=0,right=1,contractions=4,scale=72)])
        inv=quartic_invariants(f)
        self.assertEqual(packet['forms'][2]['coefficients'],[str(inv['I'])])
        self.assertEqual(packet['forms'][3]['coefficients'],[str(inv['J'])])
        import sympy as S
        x=S.Symbol('x')
        for f in ([1,0,0,1],[1,2,3,4],[0,1,0,1]):
            self.assertEqual(cubic_discriminant(f),S.discriminant(sum(v*x**i for i,v in enumerate(f)),x))
        with self.assertRaises(ValueError):compile_contractions([dict(degree=1,coefficients=[0,1])],[dict(left=1,right=0,contractions=0)])

    def test_tensor_normalization_and_alternating_sign(self):
        self.assertEqual(symmetric_tensor([1,6,3],2),(Q(1),Q(3),Q(3)))
        self.assertEqual(transvectant([0,1],1,[1,0],1,1),(Q(1),))
        self.assertEqual(transvectant([1,0],1,[0,1],1,1),(Q(-1),))
        self.assertEqual(transvectant(['1/2',1],1,[1,0],1,0),(Q(1,2),Q(1),Q(0)))

    def test_random_contractions_and_relative_covariance(self):
        rng=random.Random(917)
        for _ in range(35):
            f=[Q(rng.randrange(-20,21),rng.randrange(1,5)) for _ in range(5)]
            M=[[rng.randrange(-3,4) for _ in range(2)] for _ in range(2)]
            det=M[0][0]*M[1][1]-M[0][1]*M[1][0]
            if not det:continue
            inv=quartic_invariants(f);self.assertEqual(contraction_invariants(f),{k:inv[k] for k in ('I','J')})
            g=binary_substitute(f,4,M);new=quartic_invariants(g)
            for key,weight in [('I',4),('J',6),('discriminant',12)]:self.assertEqual(new[key],inv[key]*det**weight)
            h=quartic_covariants(f)['hessian']
            self.assertEqual(quartic_covariants(g)['hessian'],tuple(det**2*x for x in binary_substitute(h,4,M)))

    def test_independent_symbolic_discriminant_and_substitution(self):
        import sympy as S
        x,y=S.symbols('x y')
        for f in ([1,2,3,4,5],[-2,0,0,1,0],[1,0,1,0,1]):
            F=sum(a*x**i*y**(4-i) for i,a in enumerate(f));M=[[2,-1],[1,3]]
            actual=binary_substitute(f,4,M)
            expected=S.expand(F.subs({x:2*x-y,y:x+3*y},simultaneous=True))
            self.assertEqual(S.expand(expected-sum(S.Rational(a.numerator,a.denominator)*x**i*y**(4-i) for i,a in enumerate(actual))),0)
            # Degree-three affine forms still have homogeneous quartic discriminants.
            disc=S.discriminant(F.subs(y,1),x)
            if f[4]==0:disc*=f[3]**2
            self.assertEqual(quartic_invariants(f)['discriminant'],disc)

    def test_generic_transvectant_covariance(self):
        M=[[2,1],[-1,1]];det=3
        f=[Q(1,2),2,-3,1];g=[3,-1,4,0,2,1]
        for r in range(4):
            a=transvectant(binary_substitute(f,3,M),3,binary_substitute(g,5,M),5,r)
            b=binary_substitute(transvectant(f,3,g,5,r),8-2*r,M)
            self.assertEqual(a,tuple(det**r*x for x in b))

    def test_reduced_map_and_known_point(self):
        source=chart_cover(-2,C,[[1,30],[0,1]])['cover']
        reduction=reduce_cover(-2,source)
        self.assertLess(Q(reduction['score_after'][1]),Q(reduction['score_before'][1]))
        result=search_reduced_box(reduction,height=10)
        self.assertIn(['3','5'],[r['mordell_point'] for r in result['lifts']])
        self.assertFalse(reduction['global_minimality'])
        self.assertFalse(result['global_empty_proof'])

    def test_scaling_infinity_and_residue_soundness(self):
        scaled={key:[str(Q(v)*factor) for v in C[key]] for key,factor in [('quartic',4),('x_numerator',4),('y_numerator',8)]}
        reduction=reduce_cover(-2,scaled)
        self.assertLess(Q(reduction['score_after'][0]),Q(reduction['score_before'][0]))
        source=chart_cover(-2,C,[[3,1],[1,0]])['cover']
        r=reduce_cover(-2,source,max_steps=0)
        self.assertEqual(reduced_projective_lift(r,[1,0,5])['mordell_point'],['3','5'])
        for m in (8,9,16):
            self.assertIn((1%m,0),projective_residue_mask(source['quartic'],m))

    def test_invalid_domains(self):
        for values,degree in (([1.5],0),([True],0),([1,2],0)):
            with self.assertRaises(ValueError):form(values,degree)
        with self.assertRaises(ValueError):transvectant([1],0,[1],0,1)
        with self.assertRaises(ValueError):reduce_cover(-2,C,primes=(4,))


if __name__=='__main__':unittest.main()
