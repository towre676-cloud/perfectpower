"""Independent formulas, actual cover maps and boundary cases for research APIs."""
import tempfile
import unittest
from math import comb
from fractions import Fraction as Q
from perfectpower import exact_linear as E
from perfectpower.rational_functions import RationalFunction as RF
from perfectpower.parameter_functions import ParameterFunction as PF
from perfectpower.curve_families import CurveFamily
from perfectpower.multi_curve_families import MultiCurveFamily
from perfectpower.projective_deformation import projective_deformation
from perfectpower.rational_curve_quotients import discover_rational_quotients,verify_rational_quotient
from perfectpower.integral_cycle_maps import simplicial_cycle_map
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch
from perfectpower.divisor_square import WorkLimit

LEGENDRE={'coefficients':[[0],[0,1],[-1,-1],[1]]}
RECIPROCAL={'coefficients':[[1],[1],[2],[3,1],[2],[1],[1]]}
def term(powers,c=1):return {'terms':[{'powers':powers,'coefficient':c}]}
def torus(nx,ny):
    idx=lambda x,y:(x%nx)*ny+y%ny
    triangles=[]
    for x in range(nx):
        for y in range(ny):
            a,b,c,d=idx(x,y),idx(x+1,y),idx(x+1,y+1),idx(x,y+1)
            triangles.extend([[a,b,c],[a,c,d]])
    return dict(vertices=nx*ny,triangles=triangles,face_orientation_signs=[1]*len(triangles))


class ParameterAlgebra(unittest.TestCase):
    def test_exact_cancellation_and_mixed_partials(self):
        zero=PF(['a','b']);a,b=zero.variable(0),zero.variable(1)
        self.assertEqual((a*a-b*b)/(a-b),a+b)
        self.assertEqual((a+b)/(a+b),1)
        v=(a*a+b)/(a-b)
        self.assertEqual(PF.parse(['a','b'],v.packet()),v)
        self.assertEqual(v.derivative('a').derivative('b'),v.derivative('b').derivative('a'))
        self.assertEqual(v.evaluate({'a':2,'b':1}),5)
        with self.assertRaises(ValueError):v.evaluate([1,1])

    def test_specialization_removes_artificial_coefficient_poles(self):
        z=PF(['a','b','c']);a,b,c=[z.variable(i) for i in range(3)]
        v=1/(a+b*c)
        self.assertEqual(v.evaluate([1,0,2]),1)
        self.assertEqual(v.evaluate([0,1,2]),Q(1,2))
        with self.assertRaises(ValueError):v.evaluate([0,0,0])

    def test_sparse_input_and_limits(self):
        p=PF.parse(['a','b'],term([2,3],'2/3'))
        self.assertEqual(p.evaluate([2,3]),72)
        for value in (term([9,0]),term([-1,0]),term([1]),{'terms':[{'powers':[0,0],'coefficient':.5}]}):
            with self.assertRaises(ValueError):PF.parse(['a','b'],value)

    def test_fraction_free_elimination_against_rational_specializations(self):
        from perfectpower.parameter_functions import fraction_free_system
        z=PF(['a','b']);a,b=z.variable(0),z.variable(1);one=z.coerce(1)
        matrix=[[a,b,one],[one,a,one],[b,one,a+b]];rhs=[[one],[a],[b]]
        det,solution=fraction_free_system(matrix,rhs)
        for point in ([1,2],[2,3],[-1,1]):
            values=[[v.evaluate(point) for v in row] for row in matrix];target=[v[0].evaluate(point) for v in rhs]
            if E.rank(values)==3:self.assertEqual([v[0].evaluate(point) for v in solution],list(E.solve(values,target)))
        identity=[[z.coerce(int(i==j)) for j in range(3)] for i in range(3)]
        identity[0],identity[1]=identity[1],identity[0]
        self.assertEqual(fraction_free_system(identity)[0],-1)

    def test_two_parameter_elliptic_connections_against_closed_form(self):
        f=MultiCurveFamily({'parameters':['a','b'],'coefficients':[term([0,1]),term([1,0]),0,1]})
        self.assertTrue(f.evidence()['flatness'][0]['zero'])
        for a,b in ((-1,0),(1,1),(2,-3),(Q(1,3),Q(2,5))):
            a,b=Q(a),Q(b)
            data=f.specialize({'a':a,'b':b});delta=-4*a**3-27*b*b
            self.assertEqual(data['discriminant'],delta)
            expected_a=[[a*a/delta,-Q(9,2)*b/delta],[-Q(3,2)*a*b/delta,-a*a/delta]]
            expected_b=[[Q(9,2)*b/delta,3*a/delta],[a*a/delta,-Q(9,2)*b/delta]]
            self.assertEqual(data['connections']['a'],expected_a);self.assertEqual(data['connections']['b'],expected_b)
        self.assertEqual(f.observable('b')['order'],2)
        self.assertTrue(f.root_motion('a')['identity_checked'])
        self.assertEqual(f.deformation()['essential_parameter_rank'],1)
        with self.assertRaises(ValueError):f.specialize([0,0])

    def test_three_parameters_and_budget_rejection(self):
        c={'terms':[{'powers':powers,'coefficient':1} for powers in ([1,0,0],[0,1,0],[0,0,1])]}
        f=MultiCurveFamily({'parameters':['a','b','c'],'coefficients':[c,0,0,1]})
        self.assertEqual(len(f.evidence()['flatness']),3)
        data=f.specialize([1,2,3])
        for a in data['connections'].values():self.assertEqual(a,[[Q(-1,36),0],[0,Q(1,36)]])
        with self.assertRaises(WorkLimit):MultiCurveFamily({'parameters':['a','b'],'coefficients':[term([0,1]),term([1,0]),0,1],'work_limit':10})


class ProjectiveAndLocal(unittest.TestCase):
    def test_moving_infinity_projective_flow(self):
        # X^4+(Z+t X)^4: full projective motion, with varying leading term.
        p=projective_deformation({'coefficients':[[1],[0,4],[0,0,6],[0,0,0,4],[1,0,0,0,1]]})
        self.assertTrue(p['coordinate_only_generic']);self.assertTrue(p['infinity_is_movable'])
        self.assertEqual(p['quotient_dimension'],1)
        self.assertFalse(projective_deformation({'coefficients':[[0,1],[1],[0],[0],[1]]})['coordinate_only_generic'])
        with self.assertRaises(ValueError):projective_deformation({'coefficients':[[0],[0],[0],[1]]},6)
        with self.assertRaises(ValueError):projective_deformation({'coefficients':[[0],[0],[0],[0],[1]]})

    def test_legendre_multiple_discriminant_fibres_and_infinity(self):
        f=CurveFamily(LEGENDRE)
        for p in (0,1):
            a=f.local_analysis(p)
            self.assertTrue(a['fuchsian_in_diagonal_frame']);self.assertEqual(a['discriminant_valuation'],2)
            self.assertIn('2',a['finite_root_multiplicities'])
            r=[[Q(v) for v in row] for row in a['residue']]
            self.assertEqual(E.rank(r),1);self.assertFalse(any(v for row in E.multiply(r,r) for v in row))
        a=f.local_analysis('infinity');self.assertEqual(a['branch_multiplicity_at_x_infinity'],2)
        self.assertEqual(a['primitive_binary_discriminant_valuation'],2)
        self.assertEqual(a['residue_characteristic_polynomial'],['-1/4','0','1'])

    def test_analytic_legendre_jet_against_hypergeometric_coefficients(self):
        p=CurveFamily(LEGENDRE).frobenius_jet(order=12,seed=[1,0],log_degree=0)
        self.assertTrue(p['complete_requested_jet'])
        for n,row in enumerate(p['coefficients']):self.assertEqual(Q(row[0][0]),Q(comb(2*n,n)**2,16**n))
        log=CurveFamily(LEGENDRE).frobenius_jet(seed=[0,1])
        self.assertEqual(log['coefficients'][0][1],['-1/2','0'])

    def test_fractional_exponent_at_infinity_and_resonance(self):
        f=CurveFamily(LEGENDRE)
        p=f.frobenius_jet('infinity',exponent='1/2',seed=[1,'1/2'],log_degree=0)
        self.assertTrue(p['complete_requested_jet'])
        r=f.frobenius_jet('infinity',exponent='-1/2',seed=[0,1],log_degree=0)
        self.assertFalse(r['complete_requested_jet']);self.assertEqual(r['resonance_at_order'],1)
        with self.assertRaises(ValueError):f.frobenius_jet('infinity',exponent=0)

    def test_non_diagonal_irregular_frame_not_mislabeled(self):
        from perfectpower.local_curve_execution import diagonal_fuchsian_frame
        self.assertIsNone(diagonal_fuchsian_frame([[RF([1],[0,0,1])]]))
        self.assertIsNone(diagonal_fuchsian_frame([[RF([0]),RF([1],[0,0,1])],[RF([1],[0,0,1]),RF([0])]]))


class QuotientsAndProjectors(unittest.TestCase):
    def test_reciprocal_maps_and_independent_point_identity(self):
        p=discover_rational_quotients(RECIPROCAL)
        self.assertEqual(p['tested_candidates'],2);self.assertEqual(len(p['quotients']),2)
        for index,q in enumerate(p['quotients']):
            self.assertEqual(q['map_degree'],2);self.assertEqual(q['elliptic_observable']['order'],2)
            for parameter in (Q(-1),Q(0),Q(1,3)):
                coeff=[RF.parse(v).evaluate(parameter) for v in q['target_coefficients']]
                for x in (Q(1,2),Q(2),Q(-3)):
                    u=x+1/x;mult=(x+(1 if index==0 else -1))/x**2
                    source=sum(RF.parse(v).evaluate(parameter)*x**i for i,v in enumerate(RECIPROCAL['coefficients']))
                    self.assertEqual(source*mult**2,sum(v*u**i for i,v in enumerate(coeff)))

    def test_invalid_and_unsupported_quotient_candidates(self):
        invalid=dict(u_numerator=[0,1],target_degree=3)
        self.assertFalse(verify_rational_quotient(RECIPROCAL,invalid)['found'])
        with self.assertRaises(ValueError):verify_rational_quotient(RECIPROCAL,dict(u_numerator=[1],target_degree=3))
        with self.assertRaises(ValueError):verify_rational_quotient(RECIPROCAL,dict(u_numerator=[0,0,1],u_denominator=[0]))

    def test_pairing_and_projector_search_distinguish_two_families(self):
        for m in (3,5,7):
            f=CurveFamily({'coefficients':[[0,1],[-1]]+[[0]]*(m-2)+[[1]]})
            p=f.de_rham_pairing();j=[[RF.parse(v) for v in row] for row in p['pairing']]
            self.assertEqual(j[0][-1],RF([Q(4,m-2)]))
        isotrivial=CurveFamily({'coefficients':[[0,1],[0],[0],[0],[0],[1]]})
        p=isotrivial.horizontal_projectors();self.assertEqual(p['linear_space_dimension'],2)
        self.assertEqual([q['rank'] for q in p['projectors']],[2,2])
        for q in p['projectors']:self.assertTrue(all(q[k] for k in ('idempotent','horizontal','holomorphic_filtration_preserved','polarization_self_adjoint')))
        generic=CurveFamily({'coefficients':[[0,1],[-1],[0],[0],[0],[1]]})
        p=generic.horizontal_projectors();self.assertEqual(p['linear_space_dimension'],1);self.assertEqual(p['projectors'],[])

    def test_projector_checker_rejects_nonhorizontal_holomorphic_projection(self):
        f=CurveFamily(LEGENDRE);q=f.check_projector([[1,0],[0,0]])
        self.assertTrue(q['idempotent']);self.assertFalse(q['horizontal']);self.assertFalse(q['polarization_self_adjoint'])

    def test_shared_denominator_ansatz_and_query_budget_isolation(self):
        f=CurveFamily({'coefficients':[[0,1],[0],[0],[0],[0],[1]]})
        before=f.f[0].budget.work
        p=f.horizontal_projectors(degree=1,denominator=[0,1])
        self.assertEqual(p['linear_space_dimension'],2);self.assertEqual(len(p['projectors']),2)
        self.assertEqual(f.f[0].budget.work,before)


class CycleMapsAndService(unittest.TestCase):
    def test_degree_two_cover_on_actual_triangulations(self):
        s,t=torus(6,3),torus(3,3);p=simplicial_cycle_map(s,t,[(x%3)*3+y for x in range(6) for y in range(3)])
        a=p['homology_matrix'];self.assertEqual(p['degree'],2);self.assertEqual(a[0][0]*a[1][1]-a[0][1]*a[1][0],2)
        self.assertFalse(p['algebraic_cycle_identification']);self.assertTrue(p['homology_boundary_identities_checked'])

    def test_identity_orientation_and_nonsimplicial_rejection(self):
        t=torus(3,3);p=simplicial_cycle_map(t,t,list(range(9)))
        self.assertEqual(p['homology_matrix'],[[1,0],[0,1]])
        swap=simplicial_cycle_map(t,t,[y*3+x for x in range(3) for y in range(3)])
        self.assertEqual(swap['degree'],-1)
        with self.assertRaises(ValueError):simplicial_cycle_map(t,t,[0,1,2,3,4,5,6,7,9])

    def test_service_restarts_and_public_methods(self):
        with tempfile.TemporaryDirectory() as directory:
            path=directory+'/objects.sqlite'
            with Catalogue(path) as c:
                c.register('curve_family',LEGENDRE,'legendre')
                c.register('multi_curve_family',{'parameters':['a','b'],'coefficients':[term([0,1]),term([1,0]),0,1]},'universal')
            with Catalogue(path) as c:
                self.assertTrue(dispatch(c,dict(op='call',object='legendre',method='frobenius_jet',args={'seed':[1,0]}))['complete_requested_jet'])
                self.assertEqual(dispatch(c,dict(op='call',object='universal',method='summary'))['flatness_pairs'],1)
                self.assertEqual(len(dispatch(c,dict(op='discover_rational_quotients',specification=RECIPROCAL))['quotients']),2)
                with self.assertRaises(ValueError):dispatch(c,dict(op='call',object='universal',method='__init__'))


if __name__=='__main__':unittest.main()
