import copy
import unittest
from fractions import Fraction as Q
from perfectpower.mordell_three_isogeny import three_isogeny,isogeny_point,augment_isogeny_witnesses,compose_isogeny_cover
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point
from perfectpower.elliptic_certificate_verifier import verify_independence


class MordellIsogeny(unittest.TestCase):
    def test_symbolic_equation_and_differential(self):
        import sympy as S
        x,k=S.symbols('x k');X=(x**3+4*k)/x**2;factor=(x**3-8*k)/x**3
        self.assertEqual(S.cancel((x**3+k)*factor**2-X**3+27*k),0)
        self.assertEqual(S.cancel(S.diff(X,x)-factor),0)
        U=(x**3-108*k)/(9*x**2);V=(x**3+216*k)/(27*x**3)
        self.assertEqual(S.cancel((x**3-27*k)*V**2-U**3-k),0)
        self.assertEqual(S.cancel(S.diff(U,x)-3*V),0)

    def test_dual_composition_and_additivity(self):
        for k,p in [(-2,[3,5]),(-9257,[21,2]),(1,[2,3]),(-4,[2,2])]:
            E=EllipticCurve([0,k]);p=E.checked(p)
            self.assertEqual(isogeny_point(k,isogeny_point(k,p),dual=True),encode_point(E.mul(p,3)))
            a,b=E.mul(p,2),E.mul(p,3)
            partner=EllipticCurve([0,-27*k])
            self.assertEqual(isogeny_point(k,E.add(a,b)),encode_point(partner.add(isogeny_point(k,a),isogeny_point(k,b))))

    def test_kernel_and_invalid_points(self):
        self.assertIsNone(isogeny_point(1,[0,1]));self.assertIsNone(isogeny_point(-2,None))
        for k in (0,True,10**13):
            with self.assertRaises(ValueError):three_isogeny(k)
        with self.assertRaises(ValueError):isogeny_point(-2,[3,4])

    def test_positive_partner_witness_and_corruption(self):
        # Direct cubic cover of E_54; a homogeneous binary quartic with an infinity root.
        cover=dict(quartic=['54','0','0','1'],x_numerator=['0','54','0','0','1'],
            y_numerator=['2916','0','0','108','0','0','1'])
        point=isogeny_point(-2,[3,5]);u,v=Q(point[0]).numerator,Q(point[0]).denominator
        w=int(Q(point[1])*v*v)
        record=dict(partner_cover=cover,partner_coordinates=[u,v,w],partner_point=point,
            mordell_point=isogeny_point(-2,point,dual=True))
        mapping=compose_isogeny_cover(-2,cover)
        from perfectpower import polyalg as P
        t=Q(u,v);z=Q(w,v*v)
        x=P.evaluate(P.poly(map(Q,mapping['x_numerator'])),t)/P.evaluate(P.poly(map(Q,mapping['x_denominator'])),t)
        y=P.evaluate(P.poly(map(Q,mapping['y_numerator'])),t)/(z*P.evaluate(P.poly(map(Q,mapping['y_denominator'])),t))
        self.assertEqual([str(x),str(y)],record['mordell_point'])
        E=EllipticCurve([0,-2]);packet=dict(schema='pp-mordell-two-descent/1',k=-2,curve=E.specification,
            points=[],rank_upper_bound=1,witness_rank_lower_bound=0,rank_determined=False)
        result=augment_isogeny_witnesses(packet,[record]);self.assertTrue(result['rank_determined'])
        self.assertTrue(verify_independence(result['independence']))
        # Adding a redundant multiple must not force unnecessary halving.
        from unittest.mock import patch
        packet.update(points=[['3','5']],witness_rank_lower_bound=1,rank_determined=True)
        with patch.object(EllipticCurve,'halves',side_effect=AssertionError('unneeded halving')):
            result=augment_isogeny_witnesses(packet,[record])
        self.assertEqual(result['independence']['rank_lower_bound'],1)
        bad=copy.deepcopy(record);bad['mordell_point'][0]='0'
        with self.assertRaises(ValueError):augment_isogeny_witnesses(packet,[bad])


if __name__=='__main__':unittest.main()
