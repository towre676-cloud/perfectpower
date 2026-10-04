import itertools
import json
import subprocess
import sys
import unittest
from fractions import Fraction as Q
from math import gcd
from pathlib import Path
from functools import reduce
from perfectpower import exact_linear as E
from perfectpower.weighted_hodge import metric,weighted_adjoint,image_projector,constraint_projector,regularized_constraint,weighted_hodge
from perfectpower.power_sums import power_sum_witness,search_power_sums
from perfectpower.polynomial_symmetry import parse_sparse,power_coordinate,deweight,evaluate_sparse,power_composition,pullback_points,solve_power_composition
from perfectpower.finite_weil import commutant,roots,heisenberg_replay,crt_replay,degeneracy_replay
from perfectpower.divisor_square import WorkLimit

ROOT=Path(__file__).resolve().parents[2]


class WeightedHodgeTests(unittest.TestCase):
    def test_rectangular_adjoint_inner_products(self):
        d=[[1,2,-1],[0,1,3]];mx=[[2,1,0],[1,3,0],[0,0,4]];my=[[3,1],[1,2]]
        adj=weighted_adjoint(d,mx,my)
        for x in ((2,-3,1),(0,1,0)):
            for y in ((4,-2),(1,0)):
                left=sum(a*b for a,b in zip(E.apply(d,x),E.apply(my,y)))
                right=sum(a*b for a,b in zip(x,E.apply(mx,E.apply(adj,y))))
                self.assertEqual(left,right)

    def test_spd_accepts_rational_dense_metric(self):
        self.assertEqual(metric([[Q(3,2),Q(1,2)],[Q(1,2),Q(3,2)]]),((Q(3,2),Q(1,2)),(Q(1,2),Q(3,2))))

    def test_metrics_reject_bad_dimensions_indefinite_and_inexact(self):
        for m in ([[1,2],[2,1]],[[1,0],[0,0]],[[1,1],[0,1]],[[1,0,0],[0,1,0]],[[1.0]],[[True]]):
            with self.subTest(m=m),self.assertRaises(ValueError):metric(m)
        with self.assertRaises(ValueError):weighted_adjoint([[1,2]],[[1]],[[1]])

    def test_rank_deficient_image_and_zero_image(self):
        a=[[1,2,0],[2,4,0]];m=[[2,1],[1,3]];p=image_projector(a,m)
        self.assertEqual(E.multiply(p,a),E.matrix(a));self.assertEqual(E.multiply(p,p),p)
        self.assertEqual(image_projector([[0],[0]],m),((0,0),(0,0)))
        with self.assertRaises(ValueError):image_projector([[0]*65],[[1]])

    def test_constraint_image_is_complete_kernel(self):
        d=[[1,2,3],[2,4,6]];m=[[2,1,0],[1,3,0],[0,0,5]];p=constraint_projector(d,m)
        self.assertEqual(E.rank(p),3-E.rank(d))
        self.assertEqual(E.multiply(d,p),((0,0,0),(0,0,0)))
        for v in E.kernel(d):self.assertEqual(E.apply(p,v),v)

    def test_regularization_is_not_projector(self):
        p=regularized_constraint([[1,0]],E.identity(2),[[1]],1)
        self.assertEqual(p,((Q(1,2),0),(0,1)));self.assertNotEqual(E.multiply(p,p),p)
        for epsilon in (0,-1,0.5,True):
            with self.assertRaises(ValueError):regularized_constraint([[1,0]],E.identity(2),[[1]],epsilon)

    def test_weighted_chain_components_and_dense_mass(self):
        b1=[[1,-1,0]];b2=[[1],[1],[0]];m1=[[3,1,0],[1,2,0],[0,0,4]]
        p=weighted_hodge(b1,b2,[[2]],m1,[[5]])
        self.assertEqual(p['dimensions'],(1,1,1));self.assertEqual(E.rank(p['harmonic_projector']),1)
        x=(2,-3,7);parts=[E.apply(p[k],x) for k in ('gradient_projector','boundary_projector','harmonic_projector')]
        self.assertEqual(tuple(map(sum,zip(*parts))),x)
        for a,b in itertools.combinations(parts,2):self.assertEqual(sum(x*y for x,y in zip(a,E.apply(m1,b))),0)

    def test_invalid_chain_rejected(self):
        with self.assertRaises(ValueError):weighted_hodge([[1,0]],[[1],[0]],[[1]],E.identity(2),[[1]])


class PowerSumTests(unittest.TestCase):
    def test_historical_primitive_identities(self):
        for terms,target,degree in (([95800,217519,414560],422481,4),([27,84,110,133],144,5)):
            w=power_sum_witness(terms,target,degree);self.assertEqual(w['gcd'],1);self.assertTrue(w['primitive'])

    def test_normalization_and_false_identity(self):
        w=power_sum_witness([6,8,10],12,3);self.assertEqual(w['gcd'],2);self.assertEqual(w['normalized_terms'],(3,4,5))
        with self.assertRaises(ValueError):power_sum_witness([95800,217519,414561],422481,4)

    def test_complete_search_against_independent_exhaustion(self):
        for k,t,bound in itertools.product((2,3,4),(3,4),(1,4,8)):
            expected=[]
            for terms in itertools.combinations_with_replacement(range(1,bound+1),t):
                for d in range(1,bound+1):
                    if sum(x**k for x in terms)==d**k:expected.append(terms+(d,))
            got=search_power_sums(k,t,bound)
            self.assertEqual(got['solutions'],sorted(expected));self.assertTrue(got['complete_in_domain']);self.assertFalse(got['globally_complete'])

    def test_repeated_coordinates_and_primitive_filter(self):
        all_rows=search_power_sums(2,4,12)['solutions']
        self.assertIn((1,1,1,1,2),all_rows)
        expected=[r for r in all_rows if reduce(gcd,r)==1]
        self.assertEqual(search_power_sums(2,4,12,primitive_only=True)['solutions'],expected)

    def test_fail_closed_work_budget(self):
        with self.assertRaises(WorkLimit):search_power_sums(4,3,10_000)
        for args in ((True,3,4),(4,2,4),(4,3,0)):
            with self.assertRaises(ValueError):search_power_sums(*args)


class PolynomialSymmetryTests(unittest.TestCase):
    def test_sparse_parser_and_exact_evaluation(self):
        p=parse_sparse('(x-y)**3 + x*y - 7',('x','y'))
        for x,y in itertools.product(range(-3,4),repeat=2):self.assertEqual(evaluate_sparse(p,(x,y)),(x-y)**3+x*y-7)
        self.assertEqual(parse_sparse('0',('x',)),{})

    def test_parser_rejects_code_and_limits(self):
        for text in ('f(x)','x.__class__','x/2','z+x','x**-1','x**65','1.5*x','True*x'):
            with self.subTest(text=text),self.assertRaises(ValueError):parse_sparse(text,('x',))

    def test_power_quotient_roundtrip_and_obstruction(self):
        p=parse_sparse('u**3 + u*z + z**2',('u','z'))
        f=power_coordinate(power_coordinate(p,0,2),1,3)
        self.assertEqual(power_coordinate(power_coordinate(f,0,2,quotient=True),1,3,quotient=True),p)
        with self.assertRaises(ValueError):power_coordinate(p,0,2,quotient=True)
        with self.assertRaises(ValueError):power_coordinate({1:2},0,2)
        with self.assertRaises(ValueError):power_coordinate(p,0,2,quotient='yes')

    def test_deweight_identity_and_laurent_failure(self):
        p=parse_sparse('L**4*U + L**2*U**2',('U','L'))
        t=deweight(p,0,1,2,6)
        for w,l in itertools.product(range(-2,3),repeat=2):self.assertEqual(evaluate_sparse(p,(l*l*w,l)),l**6*evaluate_sparse(t,(w,l)))
        with self.assertRaises(ValueError):deweight(parse_sparse('U+1',('U','L')),0,1,2,1)

    def test_saved_hundred_term_source(self):
        p=parse_sparse((ROOT/'recovery_sources/deep_gems/PSG_Q_U_L_Z.txt').read_text(),('U','L','Z'))
        s=parse_sparse((ROOT/'recovery_sources/deep_gems/PSG_Qtilde_W_L_Z.txt').read_text(),('L','W','Z'))
        self.assertEqual(len(p),100);self.assertEqual(deweight(p,0,1,2,12),{(e[1],e[0],e[2]):c for e,c in s.items()})

    def test_even_odd_zero_and_negative_lifts(self):
        outer=[0,0,1];points=[(-8,8),(-1,-1),(0,0),(1,1),(4,4),(8,8),(9,-9)]
        even=pullback_points(outer,points,2)['points']
        self.assertEqual(even,[(-3,-9),(-2,4),(-1,1),(0,0),(1,1),(2,4),(3,-9)])
        odd=pullback_points(outer,points,3)['points']
        self.assertEqual(odd,[(-2,8),(-1,-1),(0,0),(1,1),(2,8)])

    def test_supplied_point_membership_not_completeness(self):
        row=pullback_points([0,0,1],[(4,4)],2)
        self.assertFalse(row['outer_completeness_verified_here']);self.assertTrue(row['complete_if_outer_list_complete'])
        with self.assertRaises(ValueError):pullback_points([0,0,1],[(4,3)],2)

    def test_global_solver_degree_eight_and_twelve(self):
        outer=[1,1,0,0,1]
        for q in (2,3):
            f=[0]*(4*q+1)
            for i,c in enumerate(outer):f[i*q]=c
            result=solve_power_composition(f,q)
            expected=[]
            for x in range(-30,31):
                value=x**(4*q)+x**q+1
                for y in range(-1000,1001):
                    if y*y==value:expected.append((x,y))
            self.assertEqual(result['points'],expected);self.assertTrue(result['complete'])

    def test_composition_obstruction_and_work_limit(self):
        with self.assertRaises(ValueError):power_composition([1,1,0,0,1],2)
        with self.assertRaises(WorkLimit):solve_power_composition([1,0,1,0,0,0,0,0,1],2,work_limit=1)


class FiniteWeilTests(unittest.TestCase):
    def test_exact_roots_and_fourier_heisenberg_identities(self):
        for n in (2,3,4,5,6,8,9):
            field,phase=roots(n);self.assertEqual(phase[1]**n,field.element(1))
            self.assertTrue(heisenberg_replay(n)['exact_replay'])

    def test_commutant_dimensions_include_dyadic_convention(self):
        for n,dim in ((2,1),(3,2),(4,3),(5,2),(8,5),(9,3)):
            result=commutant(n);self.assertEqual(result['dimension'],dim)
            self.assertEqual(result['equation_rank']+dim,len(result['allowed_entries']))

    def test_crt_scaled_section_is_independently_bijective(self):
        for a,b in ((2,3),(3,4),(3,5),(4,5)):
            packet=crt_replay(a,b);self.assertEqual(packet['scaled_section'],[(b*x+a*y)%(a*b) for x in range(a) for y in range(b)])
            self.assertEqual(packet['fourier_twists'],[b%a,a%b])

    def test_degeneracy_non_coprime_towers(self):
        for l,m in ((2,4),(3,6),(3,9),(4,8),(4,12)):
            p=degeneracy_replay(l,m);self.assertEqual(p['degree'],m//l);self.assertTrue(p['exact_replay'])

    def test_limits_and_invalid_levels_fail_closed(self):
        for n in (1,10,True):
            with self.assertRaises(ValueError):commutant(n)
        with self.assertRaises(WorkLimit):commutant(4,work_limit=1)
        with self.assertRaises(ValueError):crt_replay(2,4)
        with self.assertRaises(ValueError):degeneracy_replay(3,8)


class DeepCLI(unittest.TestCase):
    def test_outer_corpus_matches_stored_kernel_packets(self):
        from recover_deep_gems import audit_quartic_inputs
        corpus=json.loads((ROOT/'receipts/divisor_sum/complete_quartics.json').read_text())
        source=(ROOT/'receipts/divisor_sum/CompleteQuartics.lean').read_text()
        ledger=json.loads((ROOT/'receipts/divisor_sum/lean_catalogue_validation.json').read_text())
        self.assertEqual(audit_quartic_inputs(corpus,source,ledger)['matching_outer_packets'],3080)
        bad=json.loads(json.dumps(corpus));next(r for r in bad['rows'] if r['points'])['points'].pop()
        with self.assertRaises(ValueError):audit_quartic_inputs(bad,source,ledger)
        bad=json.loads(json.dumps(corpus));bad['rows'][0]['coefficients'][0]+=1
        with self.assertRaises(ValueError):audit_quartic_inputs(bad,source,ledger)
        with self.assertRaises(ValueError):audit_quartic_inputs(corpus,source+'\n',ledger)
        ledger['status']='PARTIAL_KERNEL_CHECK'
        with self.assertRaises(ValueError):audit_quartic_inputs(corpus,source,ledger)

    def test_new_console_routes(self):
        for args,key in ((['power-sums','--degree','3','--terms','3','--bound','6'],'solutions'),
                         (['power-composition','--coeff','[1,0,1,0,0,0,0,0,1]','--power','2'],'points'),
                         (['finite-weil','--level','2'],'dimension'),
                         (['weighted-hodge','--chain',json.dumps({'boundary1':[[0,0]],'boundary2':[[1],[0]],'mass0':[[1]],'mass1':[[1,0],[0,1]],'mass2':[[1]]})],'dimensions')):
            run=subprocess.run([sys.executable,'-m','perfectpower',*args],check=True,capture_output=True,text=True)
            self.assertIn(key,json.loads(run.stdout))


if __name__=='__main__':unittest.main()
