import random
import unittest
from fractions import Fraction as Q
from perfectpower.holomorphic_basis import differential_basis, squarefree_character_dimensions
from perfectpower import polyalg as P
from perfectpower.core import mul,power,subtract

class HolomorphicBasisTests(unittest.TestCase):
    def test_genus_two_explicit_forms(self):
        p=differential_basis([0,-1,0,0,0,1],2)
        self.assertEqual([f['numerator'] for f in p['forms_per_component']],[['1'],['0','1']])
        self.assertEqual([f['order_at_each_infinity'] for f in p['forms_per_component']],[2,0])
    def test_squarefree_grid(self):
        for d in range(2,17):
            for m in range(1,18):
                p=differential_basis([-1]+[0]*(m-1)+[1],d)
                self.assertEqual([r['holomorphic_dimension'] for r in p['characters']],squarefree_character_dimensions(d,m))
    def test_repeated_roots_and_split_components(self):
        rng=random.Random(521)
        for _ in range(160):
            f=P.poly([rng.choice([-3,1,2])]);d=rng.randrange(2,13)
            for a in rng.sample(range(-3,4),rng.randrange(1,5)):
                f=mul(f,power(P.poly([-a,1]),rng.randrange(1,10)))
            p=differential_basis(f,d)
            self.assertEqual(len(p['forms_per_component']),p['geometry']['genus_per_component'])
            self.assertEqual(sum(r['complex_h1_dimension'] for r in p['characters']),2*p['dimension_per_component'])
    def test_cancellation_of_square_factor(self):
        # z^2=(x-1)^2(x^5-x): numerator must cancel the extra root factor.
        f=mul(power(P.poly([-1,1]),2),P.poly([0,-1,0,0,0,1]))
        p=differential_basis(f,2)
        self.assertEqual(p['dimension_per_component'],2)
        self.assertEqual(p['forms_per_component'][0]['numerator'],['-1','1'])
    def test_operator_cross_multiplication(self):
        for f,d in (([0,-1,0,0,0,1],2),([-1,0,0,0,1],3),([1,0,-2,0,1],6)):
            p=differential_basis(f,d);n=p['component_equation']['power'];r=P.poly(map(Q,p['component_equation']['monic_polynomial']))
            for form in p['forms_per_component']:
                a=P.poly(map(Q,form['numerator']));j=form['character_j'];op=form['coefficient_operator']
                derivative=P.poly(map(Q,op['derivative']));zeroth=P.poly(map(Q,op['zeroth']))
                # h'/h=N'/N-jR'/(nR), clear nRN exactly.
                identity=P.add(mul(derivative,subtract(P.scale(mul(r,P.derivative(a)),n),P.scale(mul(P.derivative(r),a),j))),P.scale(mul(zeroth,mul(r,a)),n))
                self.assertTrue(P.is_zero(identity))
    def test_constants(self):
        for d in range(2,9):
            p=differential_basis([-2],d)
            self.assertEqual(p['forms_per_component'],[])
            self.assertEqual(p['geometry']['components'],d)

    def test_period_contract_attaches_actual_forms(self):
        from perfectpower.holomorphic_basis import normalize_in_basis
        p=differential_basis([0,-1,0,0,0,1],2)
        r=normalize_in_basis(p,[[2,1],[1,1]],[3,2])
        self.assertEqual(r['correction'],['-1','-1'])
        self.assertEqual(r['corrected_periods'],['0','0'])
        self.assertEqual(len(r['holomorphic_correction']),2)
        with self.assertRaises(ValueError):normalize_in_basis(p,[[1]],[0])
        with self.assertRaises(ValueError):normalize_in_basis(p,[[1,1],[1,1]],[0,0])

    def test_legendre_enclosure_nesting_and_series(self):
        from perfectpower.legendre_period_bounds import normalized_period_interval,legendre_period_packet
        for lam in (Q(0),Q(1,10),Q(1,2),Q(9,10)):
            old=normalized_period_interval(lam,8);new=normalized_period_interval(lam,32)
            self.assertLessEqual(Q(old['lower']),Q(new['lower']))
            self.assertLessEqual(Q(new['upper']),Q(old['upper']))
            self.assertLessEqual(Q(new['lower']),Q(new['upper']))
        p=legendre_period_packet(Q(1,2),80)
        self.assertLessEqual(Q(p['tau_imaginary_interval'][0]),1)
        self.assertGreaterEqual(Q(p['tau_imaginary_interval'][1]),1)
        self.assertLess(Q(p['tau_imaginary_interval'][1])-Q(p['tau_imaginary_interval'][0]),Q(1,10**24))
        a=legendre_period_packet(Q(1,3),32);b=legendre_period_packet(Q(2,3),32)
        self.assertEqual(a['real_period_over_2pi']['lower'],b['imaginary_period_over_2pi_i']['lower'])
        for lam in (-1,1,2):
            with self.assertRaises(ValueError):legendre_period_packet(lam)
