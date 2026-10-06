import io
import json
import tempfile
import unittest
from fractions import Fraction as Q
from pathlib import Path
from perfectpower import field_polynomials as F, polyalg as P
from perfectpower.rational_functions import RationalFunction as RF
from perfectpower.differential_extensions import (EtaleAlgebra,ExtensionNonUnit,
    DifferentialExtension,tensor_primitive)
from perfectpower.curve_families import CurveFamily
from perfectpower.symmetry_quotients import SymmetryCurve,PolynomialCurve,XFunction
from perfectpower.arithmetic_curve_structure import cyclotomic_polynomial
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch,serve


QUINTIC={'coefficients':[[0,1],[-1],[0],[0],[0],[1]]}
LEGENDRE={'coefficients':[[0],[0,1],[-1,-1],[1]]}
POINT={'modulus':[-256,0,0,0,3125]}
RECIPROCAL={'coefficients':[0,1,0,[0,1],0,1],
            'generators':[{'matrix':[[0,1],[1,0]],'y_scale':1}]}


def binomial(m=5):return CurveFamily({'coefficients':[[0,1]]+[[0]]*(m-1)+[[1]]})
def scalar(value):return RF.parse(value).evaluate(0)


class DifferentialAlgebraTests(unittest.TestCase):
    def test_derivative_norm_trace_and_minimal_polynomial(self):
        t=RF([0,1]);a=EtaleAlgebra([-t,0,1]);z=a.generator
        self.assertEqual(z.derivative(),1/(2*z))
        self.assertEqual(z.norm(),-t);self.assertEqual(z.trace(),0)
        self.assertEqual(z.minimal_polynomial(),[-t,t.coerce(0),t.coerce(1)])
        v=(t+1)*z+t*t
        packet=v.evidence();self.assertTrue(packet['primitive'])
        self.assertTrue(packet['derivatives'][0]['trace_identity_checked'])
        self.assertTrue(packet['derivatives'][0]['norm_log_identity_checked'])
        self.assertEqual((v*z).derivative(),v.derivative()*z+v*z.derivative())

    def test_mixed_parameter_derivations_commute(self):
        f=DifferentialExtension({'parameters':['a','b','c'],'modulus':[
            {'terms':[{'powers':[1,0,0],'coefficient':-1},{'powers':[0,1,0],'coefficient':-1},{'powers':[0,0,1],'coefficient':-1}]},0,1]})
        p=f.evidence();self.assertEqual(len(p['mixed_derivatives']),3)
        self.assertTrue(all(v['commute'] for v in p['mixed_derivatives']))
        z=f.algebra.generator
        for i in range(3):self.assertEqual(z.derivative(i),1/(2*z))

    def test_nonunit_has_a_proper_factor_and_repeated_modulus_rejected(self):
        a=EtaleAlgebra([-1,0,1]);v=a.generator-1
        with self.assertRaises(ExtensionNonUnit) as error:v.inverse()
        self.assertEqual(len(error.exception.factor),2)
        self.assertEqual(F.divide(a.modulus,error.exception.factor)[1],[a.base])
        with self.assertRaises(ValueError):EtaleAlgebra([1,-2,1])

    def test_automorphism_requires_relation_and_invertibility(self):
        a=EtaleAlgebra([-RF([0,1]),0,1])
        with self.assertRaises(ValueError):a.automorphism([0,2])
        with self.assertRaises(ValueError):a.automorphism([0])
        self.assertEqual(a.fixed_algebra([[0,-1]])['dimension'],1)

    def test_fixed_subalgebra_multiplication(self):
        a=EtaleAlgebra([-RF([0,1]),0,0,0,1]);p=a.fixed_algebra([[0,-1]])
        self.assertEqual(p['group_order'],2);self.assertEqual(p['dimension'],2)
        self.assertTrue(p['closure_checked'])
        basis=[a.element([RF.parse(c) for c in v]) for v in p['basis']]
        self.assertEqual(basis[1]*basis[1],RF([0,1]))

    def test_nested_product_automorphism_requires_a_unit_determinant(self):
        base=EtaleAlgebra([0,-1,1]);a=EtaleAlgebra([0,-1,1],base.zero)
        # z -> e*z is the identity on one component, a collapse on the other.
        # It preserves z²-z but its nonzero determinant e is a nonunit.
        with self.assertRaises(ExtensionNonUnit):
            a.automorphism(a.generator*base.generator)
        a.automorphism(1-a.generator)

    def test_hilbert90_constructs_unit_witness_and_norm_obstruction(self):
        a=EtaleAlgebra([-2,0,1]);z=a.generator
        v=(1+z)/(1-z);p=a.hilbert90([0,-1],v)
        b=a.element([RF.parse(c) for c in p['witness']])
        self.assertEqual(v,b/b.at(-z));self.assertEqual(p['status'],'DESCENDED_SCALAR')
        self.assertEqual(a.hilbert90([0,-1],[2])['status'],'NORM_OBSTRUCTION')
        self.assertEqual(a.hilbert90([0,-1],[-1])['status'],'DESCENDED_SCALAR')

    def test_hilbert90_on_split_galois_algebra_and_non_galois_rejection(self):
        a=EtaleAlgebra([-1,0,1]);p=a.hilbert90([0,-1],[Q(5,4),Q(3,4)])
        self.assertEqual(p['status'],'DESCENDED_SCALAR')
        with self.assertRaises(ValueError):EtaleAlgebra([-2,0,0,0,1]).hilbert90([0,-1],[1])

    def test_tensor_primitive_preserves_degree_and_generator_relations(self):
        p=tensor_primitive(EtaleAlgebra([-2,0,1]),EtaleAlgebra([-3,0,1]))
        self.assertEqual([scalar(v) for v in p['modulus']],[1,0,-10,0,1])
        a=EtaleAlgebra([RF.parse(v) for v in p['modulus']]);x=a.element([RF.parse(v) for v in p['left_generator']]);y=a.element([RF.parse(v) for v in p['right_generator']])
        self.assertEqual(x*x,2);self.assertEqual(y*y,3);self.assertEqual(x+y,a.generator)

    def test_repeated_field_tensor_keeps_product_components(self):
        p=tensor_primitive(EtaleAlgebra([-2,0,1]),EtaleAlgebra([-2,0,1]))
        self.assertEqual(p['degree'],4);self.assertNotEqual(p['combination_coefficient'],1)
        self.assertEqual([scalar(v) for v in p['modulus']],[36,0,-20,0,1])


class AlgebraicLocalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.f=CurveFamily(QUINTIC);cls.l=CurveFamily(LEGENDRE)

    def test_quartic_closed_point_residue_matches_nodal_formula(self):
        chart=self.f.algebraic_local_chart(POINT,order=3)
        a=EtaleAlgebra(POINT['modulus']);root=a.generator*Q(5,4)
        r=[[a.element([RF.parse(c) for c in v]) for v in row] for row in chart['residue']]
        self.assertEqual(chart['discriminant_valuation'],1);self.assertEqual(F.matrix_rank(r),1)
        self.assertFalse(any(v for row in F.matrix_product(r,r) for v in row))
        for i in range(4):
            for j in range(4):self.assertEqual(r[i][j],root**i*r[0][j])

    def test_all_finite_locations_include_repeated_discriminant_roots(self):
        p=self.l.algebraic_degenerations(order=3)
        self.assertEqual(p['covered_roots'],2)
        self.assertTrue(all(c['discriminant_valuation']==2 for c in p['charts']))
        self.assertEqual(sum(len(c['parameter']['modulus'])-1 for c in p['charts']),2)

    def test_local_point_rejects_non_squarefree_and_reports_component_nonunit(self):
        with self.assertRaises(ValueError):self.f.algebraic_local_chart({'modulus':[0,0,1]})
        with self.assertRaises(ExtensionNonUnit):self.l.algebraic_local_chart({'modulus':[0,-2,1]},order=2)

    def test_ramification_multiplies_ordinary_nodal_residue(self):
        a=self.l.algebraic_local_chart(0,order=2);b=self.l.algebraic_local_chart(0,order=2,ramification=3)
        self.assertEqual(b['discriminant_valuation'],3*a['discriminant_valuation'])
        self.assertEqual([[scalar(v) for v in row] for row in b['residue']],[[3*scalar(v) for v in row] for row in a['residue']])

    def test_legendre_resonance_is_resolved_with_nonzero_log_term(self):
        p=self.l.resonant_frobenius('infinity',order=6,exponent='-1/2',seed=[0,1])
        self.assertTrue(p['complete_requested_jet']);self.assertEqual(p['positive_resonances_resolved'],[1])
        self.assertGreater(p['log_degree'],0)
        self.assertTrue(any(scalar(v) for row in p['coefficients'][1:] for vector in row[1:] for v in vector))
        limited=self.l.resonant_frobenius('infinity',order=4,exponent='-1/2',seed=[0,1],log_degree=0)
        self.assertFalse(limited['complete_requested_jet'])

    def test_analytic_legendre_series_agrees_with_classical_binomial_coefficients(self):
        from math import comb
        p=self.l.resonant_frobenius(0,order=6,seed=[1,0],log_degree=0)
        self.assertTrue(p['complete_requested_jet'])
        self.assertEqual([scalar(row[0][0]) for row in p['coefficients']],[Q(comb(2*n,n)**2,16**n) for n in range(7)])

    def test_algebraic_logarithmic_jet_replays_at_the_nodal_point(self):
        p=self.f.resonant_frobenius(POINT,order=3,seed=[1,0,0,0])
        self.assertTrue(p['complete_requested_jet']);self.assertTrue(p['recurrence_checked'])

    def test_node_root_expansion_has_exact_quarter_second_coefficient(self):
        p=self.f.node_branches(POINT,order=4)
        # The second coefficient is 1/(20*a^4)=1/4 on every conjugate node.
        coefficient=p['branch_plus'][2]
        self.assertEqual(scalar(coefficient[0][0]),Q(1,4))
        self.assertEqual(p['branch_plus'][2],p['branch_minus'][2])
        self.assertNotEqual(p['branch_plus'][1],p['branch_minus'][1])
        self.assertEqual(p['residual_vanishes_through_order'],5)

    def test_smooth_ramified_scaling_at_zero_and_infinity(self):
        f=binomial()
        for point,sign in ((0,1),('infinity',-1)):
            p=f.ramified_scaling_chart(point)
            self.assertEqual(p['ramification'],10);self.assertEqual(p['x_scaling_exponent'],2*sign)
            self.assertEqual(p['y_scaling_exponent'],5*sign);self.assertTrue(p['special_fibre_smooth'])
            self.assertTrue(p['residue_zero']);self.assertEqual(scalar(p['unit_constant']),1)

    def test_least_scaling_ramification_changes_with_valuation(self):
        f=CurveFamily({'coefficients':[[0,0,1],[0],[0],[0],[0],[1]]})
        self.assertEqual(f.ramified_scaling_chart()['ramification'],5)


class SymmetryQuotientTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.c=SymmetryCurve(RECIPROCAL);cls.packet=cls.c.quotient()

    def test_fixed_field_generator_and_normalized_elliptic_equation(self):
        p=self.packet;self.assertEqual(p['map_degree'],2);self.assertEqual(p['target_genus'],1)
        q=[RF.parse(v) for v in p['target_coefficients']]
        self.assertEqual(q,[RF([-4,2]),RF([-2,1]),RF([2]),RF([1])])
        self.assertTrue(p['connection_intertwining_checked']);self.assertTrue(p['pullback_image_equals_projector_image'])
        v=XFunction([RF.parse(a) for a in p['v_over_y']['numerator']],[RF.parse(a) for a in p['v_over_y']['denominator']])
        expected=XFunction([RF([1]),RF([1])],[RF([0]),RF([0]),RF([1])])
        self.assertEqual(v,expected)

    def test_geometric_projector_has_all_group_and_pairing_identities(self):
        p=self.packet['projector'];self.assertEqual(p['rank'],2)
        self.assertTrue(all(p[k] for k in ('idempotent','horizontal','polarization_self_adjoint','holomorphic_filtration_preserved')))
        a=[[RF.parse(v) for v in row] for row in p['matrix']]
        self.assertEqual(F.matrix_product(a,a),a)

    def test_other_lift_has_complementary_elliptic_sector(self):
        spec={**RECIPROCAL,'generators':[{'matrix':[[0,1],[1,0]],'y_scale':-1}]}
        p=SymmetryCurve(spec).quotient();a=[[RF.parse(v) for v in row] for row in p['projector']['matrix']]
        b=[[RF.parse(v) for v in row] for row in self.packet['projector']['matrix']]
        self.assertEqual([[x+y for x,y in zip(r,s)] for r,s in zip(a,b)],[[RF([int(i==j)]) for j in range(4)] for i in range(4)])
        self.assertFalse(any(v for row in F.matrix_product(a,b) for v in row))

    def test_actual_quotient_maps_certify_degree_four_jacobian_isogeny(self):
        p=self.c.involution_decomposition()
        self.assertEqual(p['quotient_genera'],[1,1]);self.assertEqual(p['isogeny_degree'],4)
        self.assertEqual(p['kernel_annihilator'],2);self.assertEqual(p['cohomology_rank'],4)
        self.assertEqual(p['holomorphic_pullback_rank'],2)
        self.assertTrue(p['isogeny_certified'])

    def test_quotient_observable_is_minimal_order_two(self):
        p=self.c.observable('quotient');self.assertEqual(p['order'],2)
        self.assertTrue(p['operator_identity_checked']);self.assertEqual(len(p['polynomial_operator']),3)

    def test_sheet_involution_gives_genus_zero_quotient(self):
        spec={**RECIPROCAL,'generators':[{'matrix':[[0,1],[1,0]],'y_scale':1},{'matrix':[[1,0],[0,1]],'y_scale':-1}]}
        p=SymmetryCurve(spec).quotient();self.assertEqual(p['target_genus'],0);self.assertEqual(p['map_degree'],4)
        self.assertEqual(p['projector']['rank'],0)

    def test_invalid_action_and_infinite_group_budget_rejected(self):
        with self.assertRaises(ValueError):SymmetryCurve({**RECIPROCAL,'generators':[{'matrix':[[1,1],[0,1]]}]})
        with self.assertRaises(ValueError):SymmetryCurve({**RECIPROCAL,'generators':[{'matrix':[[0,0],[0,1]]}]})

    def test_independent_odd_connection_and_pairing_agree_with_existing_compiler(self):
        f=CurveFamily(QUINTIC);a=PolynomialCurve([RF.parse(v) for v in f.f],f.f[0].budget)
        self.assertEqual(a.connection,f.connection)
        self.assertEqual(matrix_packets(a.pairing()),f.de_rham_pairing()['pairing'])

    def test_even_residue_free_basis_matches_existing_sextic_engine(self):
        from perfectpower.elliptic_quotients import EllipticQuotientFamily
        spec={'coefficients':[[1],[0],[2],[0],[0,1],[0],[1]]};f=EllipticQuotientFamily(spec)
        a=PolynomialCurve([RF.parse(v) for v in f.centered],f.centered[0].budget)
        self.assertEqual(a.basis,f.basis);self.assertEqual(a.connection,f.connection)
        self.assertEqual(F.matrix_rank(a.pairing()),4)

    def test_genus_three_quotient_has_four_dimensional_sector(self):
        c=SymmetryCurve({'coefficients':[0,1,0,4,0,4,0,1],
            'generators':[{'matrix':[[0,1],[1,0]],'y_scale':-1}]})
        p=c.quotient();self.assertEqual(p['target_genus'],2);self.assertEqual(p['projector']['rank'],4)
        self.assertTrue(p['connection_intertwining_checked'])
        d=c.involution_decomposition();self.assertEqual(d['quotient_genera'],[2,1])
        self.assertEqual(d['isogeny_degree'],8);self.assertEqual(d['cohomology_rank'],6)

    def test_order_three_mobius_quotient_has_genus_zero(self):
        c=SymmetryCurve({'coefficients':[0,-1,'-25/6','-10/3','5/6',1],
            'generators':[{'matrix':[[0,-1],[1,1]],'y_scale':-1}]})
        self.assertEqual(c.summary()['group_order'],3)
        p=c.quotient();self.assertEqual(p['target_genus'],0);self.assertEqual(p['projector']['rank'],0)
        self.assertTrue(p['fixed_curve_field_certified'])

    def test_cyclotomic_coefficient_action_is_constructed_exactly(self):
        c=SymmetryCurve({'coefficients':[1,0,0,0,0,1],'coefficient_extension':[1,1,1,1,1],
            'generators':[{'matrix':[[{'algebra_coefficients':[0,1]},0],[0,1]],'y_scale':1}]})
        p=c.quotient();self.assertEqual(c.summary()['group_order'],5)
        self.assertEqual(p['target_genus'],0);self.assertEqual(p['projector']['rank'],0)


def matrix_packets(a):return [[v.packet() for v in row] for row in a]


class ArithmeticProjectorTests(unittest.TestCase):
    def test_rank_two_differential_projectors_have_rational_betti_obstructions(self):
        p=binomial().cyclic_projector_obstruction()
        self.assertEqual(p['tested_projectors'],2)
        for c in p['checks']:
            self.assertEqual(c['status'],'RATIONAL_BETTI_OBSTRUCTION')
            self.assertEqual(c['rational_character_orbits'],[[1,2,3,4]])
            self.assertIsNotNone(c['obstruction_witness'])

    def test_identity_is_rational_action_compatible(self):
        f=binomial();p=f.cyclic_projector_obstruction([[int(i==j) for j in range(4)] for i in range(4)])
        self.assertEqual(p['status'],'RATIONAL_ACTION_COMPATIBLE')

    def test_general_family_does_not_invent_cyclic_symmetry(self):
        self.assertEqual(CurveFamily(QUINTIC).cyclic_projector_obstruction()['status'],'NO_SUPPORTED_CYCLIC_SYMMETRY')

    def test_cyclotomic_factorization(self):
        for n in (3,5,6,10,14,15,30):
            f=P.ONE
            for d in range(1,n+1):
                if n%d==0:f=mul_q(f,cyclotomic_polynomial(d))
            self.assertEqual(f,P.poly([-1]+[0]*(n-1)+[1]))


def mul_q(a,b):return P.poly([sum((a[i]*b[k-i] for i in range(len(a)) if 0<=k-i<len(b)),Q(0)) for k in range(len(a)+len(b)-1)])


class ExtensionServiceTests(unittest.TestCase):
    def test_persistent_objects_recompile_and_dispatch(self):
        with tempfile.TemporaryDirectory() as path:
            db=str(Path(path)/'objects.sqlite')
            with Catalogue(db) as c:
                c.register('differential_extension',{'modulus':[{'terms':[{'powers':[1],'coefficient':-1}]},0,1]},'root')
                c.register('symmetry_curve',RECIPROCAL,'curve')
            with Catalogue(db) as c:
                p=dispatch(c,{'op':'call','object':'root','method':'evidence'});self.assertEqual(p['degree'],2)
                p=dispatch(c,{'op':'call','object':'curve','method':'summary'});self.assertEqual(p['group_order'],2)
                self.assertEqual(len(c.list()),2)

    def test_service_isolates_invalid_extension_and_keeps_running(self):
        requests=[{'op':'register','kind':'differential_extension','specification':{'modulus':[1,-2,1]}},
                  {'op':'register','kind':'curve_family','specification':LEGENDRE,'name':'l'},
                  {'op':'call','object':'l','method':'resonant_frobenius','args':{'parameter':'infinity','exponent':'-1/2','seed':[0,1],'order':3}}]
        source=io.StringIO(''.join(encoded(dict(r,request_id=i))+'\n' for i,r in enumerate(requests)));out=io.StringIO()
        with Catalogue(':memory:') as c:serve(c,source,out)
        p=[json.loads(line) for line in out.getvalue().splitlines()]
        self.assertEqual([v['ok'] for v in p],[False,True,True]);self.assertTrue(p[-1]['result']['complete_requested_jet'])


if __name__=='__main__':unittest.main()
