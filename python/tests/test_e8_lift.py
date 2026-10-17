"""Fresh exhaustive tests for the restored exact E8 adjoint lift."""
import unittest
from fractions import Fraction
from itertools import combinations

from perfectpower import e8_lift as lift
from perfectpower import e8_periods as geometry


class E8LiftTests(unittest.TestCase):
    def test_cocycle_on_every_root_pair(self):
        self.assertEqual(lift.verify_cocycle(), 57600)
        for a, b, c in zip(lift.root_coordinates()[:40], lift.root_coordinates()[40:80], lift.root_coordinates()[80:120]):
            total_ab = tuple(x+y for x, y in zip(a, b))
            total_bc = tuple(x+y for x, y in zip(b, c))
            self.assertEqual(lift.cocycle(a,b)*lift.cocycle(total_ab,c),
                             lift.cocycle(b,c)*lift.cocycle(a,total_bc))

    def test_all_lie_axioms(self):
        for i in range(248):
            self.assertEqual(lift.bracket_basis(i,i), ())
        for i,j in combinations(range(248),2):
            self.assertEqual(lift.bracket_basis(i,j),tuple((k,-c) for k,c in lift.bracket_basis(j,i)))
        self.assertEqual(lift.verify_jacobi(),2511496)

    def test_eight_sl2_normalizations(self):
        for i in range(8):
            positive=tuple(int(j==i) for j in range(8))
            e=((lift.root_basis_index(positive),1),)
            f=((lift.root_basis_index(tuple(-x for x in positive)),-1),)
            h=((i,1),)
            self.assertEqual(lift.bracket(e,f),h)
            self.assertEqual(lift.bracket(h,e),tuple((j,2*c) for j,c in e))
            self.assertEqual(lift.bracket(h,f),tuple((j,-2*c) for j,c in f))

    def test_finite_root_exponentials(self):
        for index in range(8,248):
            plus=lift.exp_ad_root(index)
            minus=lift.exp_ad_root(index,-1)
            self.assertEqual(lift.compose(plus,minus),lift.identity_map())
            self.assertTrue(all(type(c) is int for col in plus for _,c in col))
        index=lift.root_basis_index((1,0,0,0,0,0,0,0))
        half=lift.exp_ad_root(index,Fraction(1,2))
        self.assertEqual(lift.compose(half,half),lift.exp_ad_root(index))

    def test_simple_reflection_actions(self):
        cartan=geometry.cartan_matrix()
        for i in range(8):
            operator=lift.tits_lift(i)
            for root,j in zip(geometry.roots(),range(8,248)):
                target=lift.root_basis_index(geometry.simple_root_coordinates(geometry.reflect(root,geometry.SIMPLE_ROOTS[i])))
                self.assertEqual(operator[j][0][0],target)
                self.assertIn(operator[j][0][1],(-1,1))
                self.assertEqual(len(operator[j]),1)
            for j in range(8):
                expected={j:1}
                expected[i]=expected.get(i,0)-cartan[i][j]
                self.assertEqual(operator[j],tuple((k,c) for k,c in sorted(expected.items()) if c))

    def test_tits_relations(self):
        self.assertEqual(lift.verify_tits_relations(),{"square_basis_checks":1984,"braid_relations":28})

    def test_all_lift_brackets(self):
        self.assertEqual(sum(lift.verify_bracket_automorphism(lift.tits_lift(i)) for i in range(8)),245024)

    def test_actual_coxeter_spectrum_and_independent_heights(self):
        evidence=lift.receipt(exhaustive=False)
        self.assertTrue(evidence["actual_adjoint_identification_checked"])
        self.assertEqual(evidence["coxeter_negative_root_images"],128)
        self.assertEqual(evidence["simple_lift_negative_root_images"],[56]*8)
        self.assertEqual([sum(s<0 for s in o["edge_signs"]) for o in evidence["signed_root_orbits"]],[20,20,12,12,12,20,12,20])
        self.assertEqual(sum(c[0][1]<0 for c in lift.root_sign_gauge()[8:]),124)
        self.assertEqual(evidence["weight_two_pi_squared_coefficient"],"0")
        self.assertEqual(evidence["principal_height_spectrum"]["rho_squared"],"620")
        self.assertEqual(evidence["principal_height_spectrum"]["positive_roots"],120)


if __name__=="__main__":
    unittest.main()
