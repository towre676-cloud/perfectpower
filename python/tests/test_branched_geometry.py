import itertools
import random
import unittest
from perfectpower.branched_geometry import (profile,cell_surface,cyclotomic,
    faithful_laplacian,cycle_graph,transport_certificate,lift_components)
from perfectpower import polyalg as P
from perfectpower.core import mul,power


class BranchedGeometryTests(unittest.TestCase):
    def test_squarefree_genus_formula(self):
        from math import gcd
        # x^m-1 is squarefree in characteristic zero.
        for d in range(2,13):
            for m in range(1,13):
                packet=profile([-1]+[0]*(m-1)+[1],d)
                self.assertEqual(packet['components'],1)
                self.assertEqual(packet['genus_per_component'],((d-1)*(m-1)-gcd(d,m)+1)//2)
                self.assertEqual(packet['euler_total'],d+gcd(d,m)-m*(d-1))
                self.assertEqual(packet['betti'][0]-packet['betti'][1]+packet['betti'][2],packet['euler_total'])

    def test_repeated_roots_and_content_obstruction(self):
        for f,components,genus in (([0,0,0,0,0,0,1],2,0),([1,-2,1],2,0)):
            self.assertEqual(profile(f,4 if len(f)==7 else 2)['components'],components)
            self.assertEqual(profile(f,4 if len(f)==7 else 2)['genus_per_component'],genus)
        yes,no=profile([1,-2,1],2),profile([2,-4,2],2)
        self.assertTrue(yes['complex_polynomial_power']);self.assertTrue(no['complex_polynomial_power'])
        self.assertEqual(yes['integer_polynomial_root'],[-1,1]);self.assertIsNone(no['integer_polynomial_root'])
        self.assertEqual(profile([-8],3)['integer_polynomial_root'],[-2])
        self.assertIsNone(profile([-1],2)['integer_polynomial_root'])
        self.assertEqual(profile([1,4,4],2)['integer_polynomial_root'],[1,2])

    def test_random_integer_power_reconstruction(self):
        rng=random.Random(917)
        for _ in range(120):
            q=[rng.randrange(-4,5) for _ in range(rng.randrange(1,5))]
            if not any(q):q=[1]
            d=rng.randrange(2,7);f=power(P.poly(q),d);packet=profile(f,d)
            self.assertIsNotNone(packet['integer_polynomial_root'])
            self.assertEqual(power(P.poly(packet['integer_polynomial_root']),d),f)

    def test_holonomic_operator_for_actual_power(self):
        q=P.poly([3,-2,1]);d=5;f=power(q,d);packet=profile(f,d)
        result=P.add(mul(packet['holonomic_operator']['derivative_coefficient'],P.derivative(q)),
                     mul(packet['holonomic_operator']['zeroth_coefficient'],q))
        self.assertTrue(P.is_zero(result))

    def test_cyclotomic_decomposition(self):
        for d in range(1,25):
            product=P.ONE
            for k in range(1,d+1):
                if d%k==0:product=mul(product,cyclotomic(k))
            self.assertEqual(product,P.poly([-1]+[0]*(d-1)+[1]))

    def test_transport_vs_explicit_sheet_enumeration(self):
        rng=random.Random(12)
        for _ in range(150):
            d=rng.randrange(2,13);labels=[rng.randrange(-30,31) for _ in range(rng.randrange(7))]
            n,edges=cycle_graph(labels,d);packet=transport_certificate(n,edges,d)
            self.assertEqual(packet['lift_components'],len(lift_components(n,edges,d)))
            self.assertEqual(packet['faithful_character_kernel_dimension'],int(all(r%d==0 for r in labels)))

    def test_gauge_invariance(self):
        n,edges=cycle_graph([1,2,3],6);original=transport_certificate(n,edges,6)
        gauge=[(i*i+1)%6 for i in range(n)]
        changed=[(a,b,(r+gauge[b]-gauge[a])%6) for a,b,r in edges]
        other=transport_certificate(n,changed,6)
        self.assertEqual(original['cycle_residuals'],other['cycle_residuals'])
        self.assertEqual(original['lift_components'],other['lift_components'])

    def test_exact_character_laplacians(self):
        for d in range(2,9):
            for labels in ([],[d],[1],[2,4],[d,2*d],[1,2,3]):
                packet=faithful_laplacian(labels,d)
                self.assertEqual(packet['character_kernel_dimension'],int(all(r%d==0 for r in labels)))

    def test_cells_hodge_and_dual_charge(self):
        for g in range(8):
            packet=cell_surface(g)
            self.assertEqual(packet['harmonic_dimensions'],[1,2*g,1])
            self.assertEqual(packet['dual_face_charge'],12*(1-g))
            self.assertEqual(packet['curvature_over_pi'],4*(1-g))

    def test_domains_and_disconnected_graph(self):
        for f,d in (([0],2),([1],1),([1],True),([0.5,1],2)):
            with self.assertRaises((ValueError,TypeError)):profile(f,d)
        with self.assertRaises(ValueError):transport_certificate(2,[],2)
        with self.assertRaises(ValueError):faithful_laplacian([1],13)
        with self.assertRaises(ValueError):cell_surface(-1)

if __name__=='__main__':unittest.main()
