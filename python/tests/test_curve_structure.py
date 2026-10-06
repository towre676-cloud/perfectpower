"""Structural identities, independent specialization and quotient arithmetic."""
import random
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path
from perfectpower import polyalg as P, exact_linear as E, field_polynomials as F
from perfectpower.core import mul
from perfectpower.rational_functions import RationalFunction as RF, AlgebraBudget
from perfectpower.curve_families import CurveFamily
from perfectpower.elliptic_quotients import EllipticQuotientFamily, discover_elliptic_quotients, translated_even_specification
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch
from perfectpower.divisor_square import WorkLimit

GENUS_TWO=dict(coefficients=[[0,1],[-1],[0],[0],[0],[1]])
SEXTIC=dict(coefficients=[[1,1],[0],[-1],[0],[2],[0],[1]])


def shifted_sextic(center):
    budget=AlgebraBudget();z=[RF.parse(center,budget)*-1,RF.parse(1,budget)]
    polynomial=F.add(F.add(F.power(z,6),F.scale(F.power(z,4),2)),F.add(F.scale(F.power(z,2),-1),[RF([1,1],budget=budget)]))
    return dict(coefficients=[list(map(str,a.n)) for a in polynomial])


class StructuralAlgebra(unittest.TestCase):
    def test_field_polynomial_bezout_and_motion_specializations(self):
        for m in (3,5,7):
            f=CurveFamily(dict(coefficients=[[0,1],[-1]]+[[0]]*(m-2)+[[1]]))
            packet=f.root_motion();v=[RF.parse(a) for a in packet['velocity']]
            inverse=[RF.parse(a) for a in packet['bezout_inverse']]
            for t in (Q(-2),Q(0),Q(1,3)):
                p=P.poly(a.evaluate(t) for a in f.f);dx=P.derivative(p)
                speed=P.poly(a.evaluate(t) for a in v);inv=P.poly(a.evaluate(t) for a in inverse)
                self.assertEqual(P.divmod_poly(mul(dx,inv),p)[1],P.ONE)
                self.assertEqual(P.divmod_poly(P.add(P.ONE,mul(dx,speed)),p)[1],P.ZERO)

    def test_genus_two_known_velocity(self):
        f=CurveFamily(GENUS_TWO);v=[RF.parse(a) for a in f.root_motion()['velocity']]
        numerators=[[-256],[0,0,0,625],[0,0,500],[0,400],[320]]
        self.assertEqual(v,[RF(n,[-256,0,0,0,3125]) for n in numerators])

    def test_affine_quotient_and_scaling(self):
        for m in (3,5,7):
            f=CurveFamily(dict(coefficients=[[0,1]]+[[0]]*(m-1)+[[1]]))
            p=f.deformation();self.assertTrue(p['coordinate_only_generic'])
            self.assertEqual(p['quotient_dimension'],m-2)
            self.assertEqual(p['scaling_explanation']['weights'],[str(Q(i+1,m)-Q(1,2)) for i in range(m-1)])
        f=CurveFamily(GENUS_TWO);p=f.deformation();self.assertFalse(p['coordinate_only_generic'])
        self.assertNotIn('scaling_explanation',p)
        flow=[RF.parse(a) for a in p['coordinate_flow']];essential=[RF.parse(a) for a in p['essential_tangent']]
        generators=[[RF.parse(a) for a in row] for row in p['affine_orbit_generators']]
        for i,a in enumerate(f.f[:-1]):self.assertEqual(a.derivative(),essential[i]+sum(flow[j]*generators[j][i] for j in range(2)))

    def test_translated_binomial_connection_explanation(self):
        t=RF([0,1]);p=F.add(F.power([-t,RF([1])],5),[RF([1,1])])
        f=CurveFamily(dict(coefficients=[list(map(str,a.n)) for a in p]));packet=f.deformation()
        self.assertTrue(packet['coordinate_only_generic']);scaling=packet['scaling_explanation']
        self.assertEqual(RF.parse(scaling['center']),t)
        self.assertEqual(RF.parse(scaling['constant']),RF([1,1]))
        self.assertTrue(scaling['connection_identity_checked'])
        rows=scaling['centered_differential_rows']
        self.assertEqual(f.observable(rows[0])['order'],1)
        self.assertEqual(f.observable(rows[1])['order'],1)

    def test_generic_affine_basis_is_an_exact_projection(self):
        rng=random.Random(907)
        for m in (3,5):
            f=CurveFamily(dict(coefficients=[[rng.randrange(-3,4),rng.randrange(-2,3)] for _ in range(m)]+[[1]]))
            p=f.deformation();generators=[[RF.parse(a) for a in row] for row in p['affine_orbit_generators']]
            residual=[RF.parse(a) for a in p['essential_tangent']]
            for t in (Q(1,3),Q(2,3)):
                try:orbit=E.transpose([[a.evaluate(t) for a in row] for row in generators]);r=[a.evaluate(t) for a in residual]
                except ValueError:continue
                self.assertEqual(E.rank(orbit),2)
                self.assertTrue(not any(r) or E.solve(orbit,r) is None)

    def test_squarefree_algebra_units_and_factor_witness(self):
        algebra=F.SquarefreeAlgebra([0,-1,1]);t=algebra.element([0,1]);one=t.coerce(1)
        self.assertEqual((t+2)/(t+2),one)
        self.assertFalse(t*(t-1))
        with self.assertRaises(F.NonUnit) as caught:t.inverse()
        self.assertEqual(caught.exception.factor,P.X)
        with self.assertRaises(ZeroDivisionError):algebra.element([0]).inverse()
        with self.assertRaises(ValueError):F.SquarefreeAlgebra([0,0,1])
        # A field-style gcd hits a nonunit in this product algebra; the
        # collision caller must split instead of treating it as a field.
        with self.assertRaises(F.NonUnit):F.extended_gcd([t.coerce(0),t,one],[one,one])

    def test_genus_two_residue_factorization_exact(self):
        packet=CurveFamily(GENUS_TWO).collisions();self.assertEqual(packet['covered_simple_roots'],4)
        c=packet['components'][0];alg=F.SquarefreeAlgebra(c['parameter_modulus'])
        a=alg.element(c['collision_x']);tau=alg.element([0,1])
        self.assertEqual(a*4/5,tau);self.assertEqual(a*a*a*a,Q(1,5))
        u=[a.coerce(1),a,a*a,a*a*a];v=[a.coerce(-Q(3,40)),-a*a*a/8,a*a/8,3*a/8]
        expected=[[left*right for right in v] for left in u]
        residue=[[alg.element(entry) for entry in row] for row in c['residue']]
        self.assertEqual(residue,expected);self.assertEqual(c['rank'],1)
        self.assertTrue(c['square_zero']);self.assertTrue(c['image_is_collision_evaluation_line'])

    def test_cubic_and_genus_three_simple_nodes(self):
        for m in (3,7):
            f=CurveFamily(dict(coefficients=[[0,1],[-1]]+[[0]]*(m-2)+[[1]]))
            p=f.collisions();self.assertEqual(p['covered_simple_roots'],m-1)
            for c in p['components']:
                self.assertEqual(c['rank'],1);self.assertTrue(c['square_zero'])
                self.assertTrue(c['image_is_collision_evaluation_line'])

    def test_repeated_and_constant_discriminant_scope(self):
        legendre=CurveFamily(dict(coefficients=[[0],[0,1],[-1,-1],[1]])).collisions()
        self.assertEqual(legendre['covered_simple_roots'],0)
        self.assertEqual(legendre['omitted_multiple_discriminant_part'],['0','-1','1'])
        mixed=CurveFamily(dict(coefficients=[[-2,0,1],[-3],[0],[1]])).collisions()
        self.assertEqual(mixed['covered_simple_roots'],2)
        self.assertEqual(mixed['omitted_multiple_discriminant_part'],['0','1'])
        fixed=CurveFamily(dict(coefficients=[[1],[-1],[0],[1]]))
        self.assertEqual(fixed.collisions()['components'],[])
        self.assertEqual([RF.parse(a) for a in fixed.root_motion()['velocity']],[RF([0])])

    def test_collision_algebra_splits_on_nonunit_pivots(self):
        # P=(x^2-t)(x^3-x+t-2): three simple degenerations and
        # separate repeated discriminant roots from intersections of factors.
        f=CurveFamily(dict(coefficients=[[0,2,-1],[0,1],[-2,1],[-1,-1],[0],[1]]))
        packet=f.collisions();self.assertEqual(packet['covered_simple_roots'],3)
        self.assertEqual(len(packet['components']),2)
        self.assertEqual(sum(c['root_count'] for c in packet['components']),3)
        self.assertTrue(all(c['rank']==1 and c['square_zero'] for c in packet['components']))


class QuotientGeometry(unittest.TestCase):
    def test_discovery_translation_and_isolated_symmetry_locus(self):
        for center in ([0],[0,1],['1/3','1/2']):
            p=discover_elliptic_quotients(shifted_sextic(center));self.assertTrue(p['found'])
            self.assertEqual(RF.parse(p['center']),RF(center))
        p=discover_elliptic_quotients(dict(coefficients=[[1],[0],[0],[0,1],[0],[0],[1]]))
        self.assertFalse(p['found']);self.assertEqual(p['symmetry_specialization_polynomial'],['0','1'])
        p=discover_elliptic_quotients(dict(coefficients=[[1],[1],[0],[0],[0],[0],[1]]))
        self.assertFalse(p['found']);self.assertEqual(p['symmetry_specialization_polynomial'],['1'])

    def test_maps_discriminants_and_independent_specialization(self):
        q=EllipticQuotientFamily(shifted_sextic([0,1]))
        for t in (Q(0),Q(1,3),Q(1),Q(3)):
            d=q.specialize(t);p=P.poly(d['coefficients']);center=d['center']
            centered=P.compose_linear(p,center,1)
            self.assertEqual(centered,P.poly([d['C'],0,d['B'],0,d['A'],0,1]))
            self.assertEqual(P.resultant(p,P.derivative(p))*(-1)**15,P.evaluate(q.discriminant,t))
            disc=P.resultant(P.poly([d['C'],d['B'],d['A'],1]),P.poly([d['B'],2*d['A'],3]))*(-1)**3
            self.assertEqual(P.evaluate(q.discriminant,t),-64*d['C']*disc*disc)
            for z in (Q(-2),Q(1,2),Q(0),Q(3)):
                value=P.evaluate(p,center+z);u=z*z
                self.assertEqual(value,u**3+d['A']*u*u+d['B']*u+d['C'])
                if z:self.assertEqual((d['C']/z**3)**2*value,(d['C']/u)**3+d['B']*(d['C']/u)**2+d['A']*d['C']*(d['C']/u)+d['C']**2)

    def test_residue_free_basis_and_independent_reduction(self):
        q=EllipticQuotientFamily(SEXTIC);self.assertTrue(q.evidence()['connection_intertwining_checked'])
        for t in (Q(0),Q(1,3),Q(1)):
            f=P.poly(a.evaluate(t) for a in q.centered);df=P.derivative(f);dt=P.poly(a.derivative().evaluate(t) for a in q.centered)
            basis=[P.poly(a.evaluate(t) for a in row) for row in q.basis];columns=[];size=11
            for p in basis:columns.append(list(mul(p,f))+[Q(0)]*(size-len(mul(p,f))))
            for k in range(6):
                r=P.poly([0]*k+[1]);v=P.add(mul(P.derivative(r),f),P.scale(mul(r,df),-Q(1,2)))
                columns.append(list(v)+[Q(0)]*(size-len(v)))
            matrix=E.transpose(columns)
            for i,p in enumerate(basis):
                dq=P.poly(a.derivative().evaluate(t) for a in q.basis[i]);target=P.add(mul(dq,f),P.scale(mul(p,dt),-Q(1,2)))
                answer=E.solve(matrix,list(target)+[Q(0)]*(size-len(target)))
                self.assertEqual(answer[:4],tuple(a.evaluate(t) for a in q.connection[i]))
        self.assertEqual(q.observable()['operator']['order'],2)
        self.assertEqual(q.observable('second')['operator']['order'],2)

    def test_varying_coefficients_and_parameter_derivative_of_basis(self):
        q=EllipticQuotientFamily(dict(coefficients=[[1,0,1],[0],[1,1],[0],[2,1],[0],[1]]))
        self.assertTrue(q.evidence()['connection_intertwining_checked'])
        self.assertEqual(q.basis[3][2].derivative(),RF([Q(1,2)]))
        self.assertEqual(q.observable()['operator']['order'],2)
        # At infinity, eta_3=(z^4+A z^2/2) dz/y has its 1/z term canceled.
        self.assertEqual(q.basis[3][2],q.A/2)

    def test_rational_point_images_lifts_and_integrality(self):
        q=EllipticQuotientFamily(shifted_sextic([0,1]));image=q.point_image(1,2,2)
        self.assertEqual(image['first'],[Q(1),Q(2)]);self.assertEqual(image['second_cubic'],[Q(2),Q(4)])
        for sector in ('first','second'):
            p=q.rational_lifts(1,1,2,sector)
            self.assertTrue(p['complete_rational_fibre']);self.assertEqual(len(p['points']),2)
            self.assertTrue(all(r['integral'] for r in p['points']))
            for r in p['points']:self.assertEqual(q.point_image(1,r['x'],r['y'])[sector if sector=='first' else 'second_quartic'],[1,2])
        exceptional=q.point_image(0,0,1);self.assertTrue(exceptional['second_cubic_at_infinity'])
        self.assertEqual(len(q.rational_lifts(0,0,0,'second')['points']),2)
        translated=EllipticQuotientFamily(shifted_sextic([0,'1/2']))
        self.assertTrue(all(not r['integral'] for r in translated.rational_lifts(3,0,2)['points']))

    def test_nonsquare_rational_fibres_and_invalid_points(self):
        # A quotient point with rational y and nonsquare u has no rational lift.
        q=EllipticQuotientFamily(dict(coefficients=[[1],[0],[-4],[0],[0],[0],[1]]))
        self.assertEqual(q.rational_lifts(0,2,1)['points'],[])
        q=EllipticQuotientFamily(dict(coefficients=[['115/64'],[0],[-1],[0],[0],[0],[1]]))
        self.assertEqual(q.rational_lifts(0,'1/4','5/4')['points'][0]['x'],Q(-1,2))
        # A quotient point can have rational y but a nonsquare denominator in u.
        q=EllipticQuotientFamily(dict(coefficients=[['7/8'],[0],[0],[0],[0],[0],[1]]))
        self.assertEqual(q.rational_lifts(0,'1/2',1)['points'],[])
        with self.assertRaises(ValueError):q.point_image(0,0,0)
        with self.assertRaises(ValueError):q.rational_lifts(0,0,0)
        with self.assertRaises(ValueError):q.observable('bad')

    def test_service_restart_discovery_and_private_method_rejection(self):
        with tempfile.TemporaryDirectory() as directory:
            path=str(Path(directory)/'structure.sqlite')
            with Catalogue(path) as c:
                c.register('curve_family',GENUS_TWO,'moving');c.register('elliptic_quotient',SEXTIC,'split')
            with Catalogue(path) as c:
                self.assertEqual(dispatch(c,dict(op='call',object='moving',method='collisions'))['covered_simple_roots'],4)
                self.assertEqual(dispatch(c,dict(op='call',object='split',method='observable'))['operator']['order'],2)
                self.assertTrue(dispatch(c,dict(op='discover_quotients',specification=shifted_sextic([0,1])))['found'])
                built=dispatch(c,dict(op='construct_quotient',args=dict(A=2,B=-1,C=[1,1],center=[0,1])))
                self.assertEqual(EllipticQuotientFamily(built['specification']).center,RF([0,1]))
                with self.assertRaises(ValueError):dispatch(c,dict(op='call',object='split',method='_reduce'))

    def test_construct_from_elliptic_quotient(self):
        spec=translated_even_specification(A=2,B=-1,C=[1,1],center=[0,1])
        self.assertEqual(spec,shifted_sextic([0,1]))
        q=EllipticQuotientFamily(spec)
        self.assertEqual(q.sectors['first'].f,[RF([1,1]),RF([-1]),RF([2]),RF([1])])

    def test_contracts_budgets_and_singular_sextics(self):
        for spec in (dict(coefficients=[[1]]*6),dict(coefficients=[[1],[1],[0],[0],[0],[0],[1]]),
            dict(coefficients=[[0],[0],[1],[0],[0],[0],[1]]),dict(coefficients=[[1],[0],[3],[0],[3],[0],[1]])):
            with self.assertRaises(ValueError):EllipticQuotientFamily(spec)
        with self.assertRaises(WorkLimit):EllipticQuotientFamily(dict(SEXTIC,work_limit=20))
        with self.assertRaises(ValueError):discover_elliptic_quotients(dict(coefficients=[[1.2],[0],[0],[0],[0],[0],[1]]))
        with self.assertRaises(ValueError):EllipticQuotientFamily(SEXTIC).specialize(-1)

    def test_quotient_sector_period_continuation(self):
        try:import numpy,scipy
        except ImportError:self.skipTest('optional numerical backend')
        q=EllipticQuotientFamily(dict(coefficients=[[-1,1],[0],[-1],[0],[0],[0],[1]]))
        for sector,mark in [('first',dict(center=['-2/3',0],radius='1')),
            ('second',dict(center=['7/8',0],radius='4/5'))]:
            f=q._sector(sector)
            result=q.period_path([0,'1/20'],mark,sector=sector)['continuation']
            self.assertGreater(abs(complex(*result['initialization']['period_vector'][0])),1e-5)
            direct=f.marked_period('1/20',mark)
            error=max(abs(complex(*a)-complex(*b)) for a,b in zip(result['trajectory'][-1]['state'],direct['period_vector']))
            self.assertLess(error,1e-8)


if __name__=='__main__':unittest.main()
