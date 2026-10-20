import unittest
from fractions import Fraction as Q
from perfectpower.coxeter_normalizer import (ALPHA,field_product,galois_matrix,lattice_data,
    multiplication_matrix,determinant,normalizer_lifts,verify_lift,receipt,nonsplit_certificate)
from perfectpower.e8_periods import matvec,identity,matrix_power,roots,simple_root_coordinates

class NormalizerTests(unittest.TestCase):
    def test_trace_form(self):
        r=receipt()['trace_form']
        self.assertEqual(r['norm_alpha'],'1/1265625')
        self.assertEqual(r['field_discriminant'],'1265625')
        self.assertEqual(field_product(ALPHA,tuple(map(Q,r['inverse_alpha']))),(1,0,0,0,0,0,0,0))
        x=(1,-2,0,3,-1,4,0,2);y=(3,1,-1,0,5,0,-2,1)
        z=field_product(ALPHA,field_product(x,matvec(galois_matrix(29),y)))
        self.assertEqual(sum(multiplication_matrix(z)[i][i] for i in range(8)),sum(u*v for u,v in zip(x,matvec(lattice_data()[-1],y))))
    def test_complete_normalizer(self):
        rs={simple_root_coordinates(r) for r in roots()}
        self.assertEqual(len(normalizer_lifts()),240)
        for e,u in normalizer_lifts():
            self.assertTrue(verify_lift(e,u));self.assertEqual(abs(determinant(u)),1)
        for e in (1,7,11,13,17,19,23,29):
            u=next(u for a,u in normalizer_lifts() if a==e)
            self.assertEqual({matvec(u,r) for r in rs},rs)
        self.assertEqual(receipt()['root_orbit_sizes'],[120,120])
    def test_nonsplit(self):
        r=nonsplit_certificate()
        self.assertFalse(r['extension_splits'])
        self.assertEqual(matrix_power(r['lift'],4),matrix_power(lattice_data()[0],25))
        counts={8:0,24:0}
        for e,u in normalizer_lifts():
            if e==7:
                n=next(k for k in (1,2,3,4,6,8,12,24) if matrix_power(u,k)==identity())
                counts[n]+=1
        self.assertEqual(counts,{8:10,24:20})
    def test_reject_false_maps(self):
        self.assertTrue(verify_lift(1,identity()))
        self.assertFalse(verify_lift(7,identity()))
        self.assertFalse(verify_lift(2,identity()))
        u=[list(r) for r in identity()];u[0][0]=2
        self.assertFalse(verify_lift(1,u))
        u[0][0]=Q(1,2);self.assertFalse(verify_lift(1,u))

if __name__=='__main__':unittest.main()
