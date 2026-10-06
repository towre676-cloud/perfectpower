import json
import tempfile
import unittest
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
from perfectpower.rational_functions import RationalFunction as RF
from perfectpower.differential_modules import DifferentialModule
from perfectpower.superelliptic_families import SuperellipticFamily
from perfectpower.curve_correspondences import genus_three_elliptic_tower,richelot_correspondence
from perfectpower.formal_isogenies import elliptic_two_isogeny
from perfectpower.marked_curve_topology import braid_monodromy,reflection_kernel
from perfectpower.root_cluster_geometry import cluster_geometry,simultaneous_quadratic_nodes
from perfectpower.binomial_periods import BinomialSum
from perfectpower.sunrise_relative import sunrise_certificate
from perfectpower.certified_period_transport import certified_transport,legendre_marked_periods,Gaussian
from perfectpower.arithmetic_frobenius import frobenius_matrix,zeta_by_counting,frobenius_deformation,tower_frobenius,modular,characteristic
from perfectpower.exact_linear import multiply,identity
from perfectpower.catalogue import Catalogue,encoded
from perfectpower.query_service import dispatch


def decoded(packet):return [[RF.parse(v) for v in row] for row in packet['connection']]


class DifferentialTensorTests(unittest.TestCase):
    def test_tensor_dual_and_hom_conventions(self):
        a=DifferentialModule({'matrix':[[1,2],[3,4]]});b={'matrix':[[5]]}
        self.assertEqual(decoded(a.tensor(b)),[[RF([6]),RF([2])],[RF([3]),RF([9])]])
        self.assertEqual(decoded(a.dual()),[[RF([-1]),RF([-3])],[RF([-2]),RF([-4])]])
        h=DifferentialModule({'matrix':a.hom(a.specification)['connection']})
        self.assertEqual(h.horizontal_sections(degree=0)['dimension'],2)

    def test_exterior_determinant_and_symmetric_square(self):
        m=DifferentialModule({'matrix':[[1,2],[3,4]]})
        self.assertEqual(decoded(m.power(2,True)),[[RF([5])]])
        self.assertEqual(decoded(m.power(2)),[[RF([8]),RF([6]),RF([0])],[RF([2]),RF([5]),RF([3])],[RF([0]),RF([4]),RF([2])]])

    def test_parameter_chain_rule(self):
        m=DifferentialModule({'matrix':[[[0,1]]]})
        self.assertEqual(decoded(m.pullback([0,0,1])),[[RF([0,0,0,2])]])

    def test_rational_section_requires_declared_denominator(self):
        m=DifferentialModule({'matrix':[[{'numerator':[-1],'denominator':[0,1]}]]})
        self.assertEqual(m.horizontal_sections(1)['dimension'],0)
        self.assertEqual(m.horizontal_sections(0,[0,1])['dimension'],1)

    def test_gauge_and_nontrivial_matrix_descent(self):
        m=DifferentialModule({'matrix':[[0,1],[[0,0,1],0]]})
        r=m.involution_descent([[1,0],[0,-1]])
        a=decoded(r['descended'])
        self.assertEqual(a[0][1],RF([Q(1,2)],[0,1]));self.assertEqual(a[1][0],RF([0,Q(1,2)]))
        with self.assertRaises(ValueError):m.involution_descent([[2,0],[0,1]])
        with self.assertRaises(ValueError):m.gauge([[1,0],[0,0]])

    def test_filtered_polarized_space(self):
        m=DifferentialModule({'matrix':[[0,0],[0,0]]})
        self.assertEqual(m.horizontal_endomorphisms(holomorphic_indices=[0])['linear_space_dimension'],3)
        r=m.horizontal_endomorphisms(holomorphic_indices=[0],pairing=[[0,1],[-1,0]])
        self.assertEqual(r['linear_space_dimension'],1);self.assertEqual(r['projectors'],[])

    def test_allocation_guards(self):
        m=DifferentialModule({'matrix':[[0]*7 for _ in range(7)]})
        with self.assertRaises(ValueError):m.tensor(m.specification)
        with self.assertRaises(ValueError):m.power(4)


class SuperellipticTests(unittest.TestCase):
    def test_hyperelliptic_special_case_agrees(self):
        from perfectpower.symmetry_quotients import PolynomialCurve
        f=[RF([0,1]),RF([1]),RF([0]),RF([1])]
        s=SuperellipticFamily({'coefficients':[v.packet() for v in f],'cover_degree':2})
        self.assertEqual(s.connection,PolynomialCurve(f,s.budget).connection)

    def test_trigonal_hodge_and_character_blocks(self):
        s=SuperellipticFamily({'coefficients':[[0,1],1,0,0,1],'cover_degree':3});e=s.evidence()
        self.assertEqual(s.genus,3);self.assertEqual(sum(v['holomorphic'] for v in e['basis']),3)
        self.assertFalse(any(s.connection[i][j] for i in range(6) for j in range(6) if i//3!=j//3))
        self.assertEqual(s.observable()['order'],3)

    def test_repeated_pole_primitives_replay(self):
        s=SuperellipticFamily({'coefficients':[[0,1],1,0,0,1],'cover_degree':3})
        c,r=s.reduce([s.zero.coerce(1)],2,3)
        self.assertEqual(len(c),3);self.assertTrue(r)

    def test_scope_rejections(self):
        for spec in ({'coefficients':[1,0,0,1],'cover_degree':3},{'coefficients':[0,0,0,1],'cover_degree':2},{'coefficients':[1,1,0,2],'cover_degree':2}):
            with self.assertRaises(ValueError):SuperellipticFamily(spec)


class CorrespondenceTests(unittest.TestCase):
    def test_formal_lifting_recovers_map_not_just_jets(self):
        for a,b in ((1,2),(0,1),(3,1)):
            r=elliptic_two_isogeny(a,b);self.assertEqual(r['map_degree'],2)
            coefficients=r['x_map']['numerator'];self.assertEqual([RF.parse(v).evaluate(0) for v in coefficients],[b,a,1])
            self.assertEqual(r['kernel_point'],['0','0']);self.assertTrue(r['differential_identity_checked'])

    def test_bad_formal_models_rejected(self):
        with self.assertRaises(ValueError):elliptic_two_isogeny(2,1)

    def test_richelot_correspondence_and_divisor_kernel(self):
        r=richelot_correspondence([[1,1,1],[3,2,1],[7,3,1]])
        self.assertEqual(RF.parse(r['determinant']),-2);self.assertEqual(r['kernel_invariant_factors'],[2,2]);self.assertTrue(r['correspondence_ideal_identity_checked'])

    def test_degenerate_richelot_split_requires_distinct_construction(self):
        with self.assertRaises(ValueError):richelot_correspondence([[-1,0,1],[-4,0,1],[-9,0,1]])

    def test_reflection_kernel_has_actual_torus_generators(self):
        r=reflection_kernel();self.assertEqual(r['kernel_invariant_factors'],[2,2])
        for v in r['kernel_generators']:
            point=list(map(Q,v['source_torus_coordinates']))
            self.assertTrue(any(point));self.assertTrue(all((2*x).denominator==1 for x in point))
            self.assertTrue(all(sum(Q(x)*y for x,y in zip(row,point)).denominator==1 for row in r['norm']))

    def test_braid_word_cancellation_and_relations(self):
        for g in (1,2,3,4):
            self.assertEqual(braid_monodromy(g,[1,-1])['matrix'],[list(map(int,row)) for row in identity(2*g)])
        self.assertEqual(braid_monodromy(2,[1,2,1])['matrix'],braid_monodromy(2,[2,1,2])['matrix'])


class ClusterTests(unittest.TestCase):
    def test_even_clusters_make_graph_cycles(self):
        r=cluster_geometry([0,3,1,4,2,5],3);self.assertEqual(r['total_genus'],2);self.assertEqual(r['graph_cycle_rank'],2)

    def test_odd_cluster_makes_component_genus(self):
        r=cluster_geometry([0,3,6,1,2],3);self.assertEqual(r['total_genus'],2);self.assertEqual(r['graph_cycle_rank'],0)

    def test_nested_cluster_and_negative_depth(self):
        r=cluster_geometry(['0','1/3','1','4','13'],3);self.assertEqual(r['total_genus'],2);self.assertEqual(r['clusters'][0]['depth'],-1)

    def test_simultaneous_degenerations(self):
        r=simultaneous_quadratic_nodes([0,3,7]);self.assertEqual(r['contact_orders'][0][1],1);self.assertEqual(r['contact_orders'][0][2],0)

    def test_bad_cluster_domains(self):
        for roots,p in (([0,1,2],2),([0,0,1],3),([0,1,2],9)):
            with self.assertRaises(ValueError):cluster_geometry(roots,p)


class BinomialAndRelativeTests(unittest.TestCase):
    def test_constant_term_affine_compiler_and_values(self):
        b=BinomialSum({'factors':[[1,0,0,0,1,0]]});self.assertEqual(b.terms(size=6),[1,2,4,8,16,32]);self.assertIn('CT_z',b.evidence()['constant_term']['generating_function'])

    def test_telescopers_including_upper_boundary(self):
        from math import comb
        for name in ('vandermonde','apery2','apery3'):
            b=BinomialSum({'family':name});certificate=b.telescoper()['shift_certificate'];polys=[RF.parse(v) for v in certificate['numerator_k_coefficients']]
            def term(n,k):
                if not 0<=k<=n:return 0
                v=comb(n,k)**2
                return v*(comb(n+k,k)**(0 if name=='vandermonde' else (1 if name=='apery2' else 2)))
            for n in range(1,6):
                def G(k):
                    if k==0 or k>n+1:return Q(0)
                    P=sum(v.evaluate(n)*k**i for i,v in enumerate(polys))
                    if name=='vandermonde':return Q(factorial(n)**2,factorial(k-1)**2*factorial(n-k+1)**2)*P
                    if name=='apery2':return Q(factorial(n)*factorial(n+k-1),factorial(k-1)**3*factorial(n-k+1)**2)*P
                    return Q(factorial(n+k-1)**2,factorial(k-1)**4*factorial(n-k+1)**2)*P
                for k in range(n+2):
                    if name=='vandermonde':L=(n+1)*term(n+1,k)-2*(2*n+1)*term(n,k)
                    elif name=='apery2':L=(n+1)**2*term(n+1,k)-(11*n*n+11*n+3)*term(n,k)-n*n*term(n-1,k)
                    else:L=(n+1)**3*term(n+1,k)-(2*n+1)*(17*n*n+17*n+5)*term(n,k)+n**3*term(n-1,k)
                    self.assertEqual(L,G(k+1)-G(k),(name,n,k))

    def test_apery_sequence_has_geometric_period_operator(self):self.assertTrue(BinomialSum({'family':'apery2'}).elliptic_bridge()['operator_identity_checked'])

    def test_sunrise_absolute_and_relative_are_distinct_states(self):
        r=sunrise_certificate();self.assertEqual(r['period_operator']['order'],2);self.assertEqual(r['relative_module']['dimension'],3)
        self.assertEqual(r['boundary']['integrated_value'],-6);self.assertTrue(r['exact_divergence_identity_checked'])


class CertifiedExecutionTests(unittest.TestCase):
    def test_scalar_exponential_inside_exact_enclosure(self):
        r=certified_transport([[1]],['0','1/8'],8);value=Q(r['matrix'][0][0][0]);error=Q(r['row_error_bound'])
        partial=sum(Q(1,8**k*factorial(k)) for k in range(32));tail=Q(1,8**32*factorial(32))*Q(264,263)
        self.assertLessEqual(abs(value-partial)+tail,error)

    def test_complex_transport_and_zero_solution(self):
        r=certified_transport([[0]],[[0,0],['1/8','1/8']],8);self.assertEqual(r['matrix'],[[['1','0']]])

    def test_marked_seed_and_period_bounds(self):
        r=legendre_marked_periods(['1/2','9/16'],8);self.assertTrue(r['seed_certified']);self.assertLess(Q(r['row_error_bound']),Q(1,1000));self.assertEqual(len(r['period_state']),2)

    def test_pole_and_work_exhaustion_reject(self):
        with self.assertRaises(ValueError):certified_transport([[{'numerator':[1],'denominator':[0,1]}]],['0','1'],8)
        with self.assertRaises(ValueError):certified_transport([[{'numerator':[1],'denominator':[0,1]}]],['1','2'],8,step_limit=1)


class ArithmeticTests(unittest.TestCase):
    def test_frobenius_matrix_matches_independent_elliptic_count(self):
        for coefficients,p in (([1,1,0,1],5),([1,0,0,1],7),([0,-1,0,1],5)):
            r=frobenius_matrix(coefficients,p);c=zeta_by_counting(coefficients,p)
            self.assertEqual(r['characteristic_residues'],[v%(p*p) for v in c['weil_polynomial_high_to_low']]);self.assertTrue(r['precision_certified'])

    def test_two_precisions_reduce_to_same_matrix(self):
        a=frobenius_matrix([1,1,0,1],5,1);b=frobenius_matrix([1,1,0,1],5,2)
        self.assertEqual(a['matrix'],[[v%5 for v in row] for row in b['matrix']])

    def test_genus_two_extension_counts_and_functional_equation(self):
        c=zeta_by_counting([1,-1,0,0,0,1],7);poly=c['weil_polynomial_high_to_low']
        self.assertEqual(poly[-1],49);self.assertEqual(poly[-2],7*poly[1]);self.assertEqual(len(c['extension_counts']),2)
        r=frobenius_matrix([1,-1,0,0,0,1],7,1);self.assertEqual(r['characteristic_residues'],[v%7 for v in poly])

    def test_frobenius_deformation_precision_and_base(self):
        r=frobenius_deformation([[1,1],1,0,1],5,2,6)
        self.assertEqual(r['base_frobenius']['precision'],3);self.assertEqual(r['jets'][-1]['scale'],5);self.assertEqual(r['jets'][-1]['absolute_precision'],2)

    def test_bad_reduction_and_precision_domains(self):
        with self.assertRaises(ValueError):frobenius_matrix([0,0,0,1],5)
        with self.assertRaises(ValueError):frobenius_deformation([[1,1],1,0,1],1)


class IntegratedTowerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.tower=genus_three_elliptic_tower()
    def test_composed_maps_span_all_cohomology(self):
        self.assertEqual(self.tower['cohomology_rank'],6);self.assertEqual(self.tower['holomorphic_rank'],3);self.assertEqual(self.tower['isogeny_degree'],32)
        self.assertEqual([v['map_degree'] for v in self.tower['maps']],[2,4,4])
    def test_structure_accelerated_frobenius_matches_independent_counts(self):
        r=tower_frobenius(self.tower);self.assertEqual(r['source_zeta']['weil_polynomial_high_to_low'],[1,0,5,0,35,0,343]);self.assertTrue(r['independent_counts_match'])
    def test_forged_pullback_receipt_cannot_supply_geometric_evidence(self):
        fake=json.loads(json.dumps(self.tower));fake['pullback'][0][0]={'numerator':['0'],'denominator':['1']}
        with self.assertRaises(ValueError):tower_frobenius(fake)


class PersistentResearchTests(unittest.TestCase):
    def test_three_new_kinds_and_standalone_queries_survive_cold_reload(self):
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'catalogue.sqlite'
            with Catalogue(path) as c:
                c.register('differential_module',{'matrix':[[0,1],[-1,0]]},'module')
                c.register('superelliptic_family',{'coefficients':[[0,1],1,0,0,1],'cover_degree':3},'trigonal')
                c.register('binomial_sum',{'family':'apery2'},'apery')
            with Catalogue(path) as c:
                self.assertEqual(dispatch(c,{'op':'call','object':'module','method':'power','args':{'degree':2,'exterior':True}})['dimension'],1)
                self.assertEqual(dispatch(c,{'op':'call','object':'trigonal','method':'summary'})['genus'],3)
                self.assertEqual(dispatch(c,{'op':'call','object':'apery','method':'terms','args':{'size':3}}),[1,3,19])
                self.assertEqual(dispatch(c,{'op':'reflection_kernel'})['isogeny_degree'],4)
                self.assertTrue(dispatch(c,{'op':'formal_two_isogeny','args':{'a':1,'b':2}})['algebraic_identity_checked'])


if __name__=='__main__':unittest.main()
