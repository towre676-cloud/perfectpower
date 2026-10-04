import copy
import itertools
import json
import random
import subprocess
import sys
import unittest
from fractions import Fraction as Q
from pathlib import Path
from perfectpower import polyalg as P
from perfectpower import exact_linear as E
from perfectpower.core import integer_power_root
from perfectpower.divisor_square import WorkLimit
from perfectpower.sturm_fibres import root_certificate,verify_roots,square_fibres,verify_square_fibres
from perfectpower.sharp_power_gap import sharp_bound,verify_bound,scan_sharp
from perfectpower.residue_cover import residue_cover,evaluate
from perfectpower.arithmetic_engine import ArithmeticEngine,verify_result,affine_power_reductions
from perfectpower.compiler import PowerConstraint,compile_constraint
from perfectpower.connection_polytope import ConnectionGraph,root_channel_graph
from perfectpower.connection_measure import ConnectionMeasure,verify_measure,verify_conditioning
from perfectpower.operator_algebra import generated_algebra,verify_algebra,algebra_profile,verify_profile,algebra_membership,verify_membership

ROOT=Path(__file__).resolve().parents[2]


class SturmCertificates(unittest.TestCase):
    def test_random_polynomials_against_independent_small_scan(self):
        rng=random.Random(194)
        for _ in range(100):
            f=[rng.randint(-6,6) for _ in range(rng.randint(2,7))];f[-1]=rng.choice([-3,-1,1,3])
            r=root_certificate(f,lo=-20,hi=20)
            self.assertEqual(r['roots'],[x for x in range(-20,21) if evaluate(f,x)==0]);self.assertTrue(verify_roots(r))

    def test_giant_roots_repetition_and_noninteger_boundaries(self):
        n=10**100;f=P.mul(P.power(P.poly([-n,1]),3),P.mul(P.poly([1,2]),P.poly([1,0,1])))
        r=root_certificate(map(int,f));self.assertEqual(r['roots'],[n]);self.assertLess(r['nodes_checked'],6000)
        self.assertTrue(verify_roots(json.loads(json.dumps(r))))
        for lo,hi,expected in ((n,n,[n]),(n+1,n+2,[]),(-1,0,[])):
            self.assertEqual(root_certificate(map(int,f),lo=lo,hi=hi)['roots'],expected)

    def test_negative_zero_and_endpoint_roots(self):
        f=[0,0,2,-3,1]
        for lo,hi in ((0,2),(-10,0),(1,1),(3,100),(-3,-1)):
            r=root_certificate(f,lo=lo,hi=hi);self.assertTrue(verify_roots(r))
            self.assertEqual(r['roots'],[x for x in (0,1,2) if lo<=x<=hi])
        self.assertTrue(verify_roots(root_certificate([-5])))

    def test_budget_and_bad_inputs(self):
        with self.assertRaises(WorkLimit):root_certificate([-10**100,1],node_limit=1)
        for f in ([0],[1.0,1],[True,1]):
            with self.assertRaises(ValueError):root_certificate(f)
        with self.assertRaises(ValueError):root_certificate([1,1],lo=2,hi=1)

    def test_transcript_tamper_and_missing_branches(self):
        r=root_certificate([0,0,2,-3,1]);self.assertTrue(verify_roots(r))
        variants=[]
        x=copy.deepcopy(r);x['roots']=[0,1];variants.append(x)
        x=copy.deepcopy(r);x['nodes'].pop();variants.append(x)
        x=copy.deepcopy(r);x['nodes'][0][2]+=1;variants.append(x)
        x=json.loads(json.dumps(r));x['sturm_chain'][-1][0]*=-1;variants.append(x)
        x=copy.deepcopy(r);x['squarefree_factors'][0][0]+=1;variants.append(x)
        x=copy.deepcopy(r);x['root_bound']=True;variants.append(x)
        x=copy.deepcopy(r);x['execution_verified']=True;variants.append(x)
        for x in variants:self.assertFalse(verify_roots(x))

    def test_square_fibres_complete_far_apart(self):
        n=10**100;r=square_fibres([n,-n-1,1],1)
        self.assertEqual(r['points'],[(1,-1),(1,1),(n,-1),(n,1)]);self.assertLess(r['work_used'],1500)
        self.assertTrue(verify_square_fibres(json.loads(json.dumps(r))))
        x=copy.deepcopy(r);x['fibres']=[];self.assertFalse(verify_square_fibres(x))
        x=copy.deepcopy(r);x['parameters'].pop();self.assertFalse(verify_square_fibres(x))
        with self.assertRaises(WorkLimit):square_fibres([n,-n-1,1],1,work_limit=1)
        with self.assertRaises(WorkLimit):square_fibres([0,1],10**30)

    def test_signed_constants_against_independent_finite_scan(self):
        for f,k in itertools.product(([1,2,1],[-1,0,1],[2,1,0,1]),(-8,-3,1,8)):
            r=square_fibres(f,k);self.assertTrue(verify_square_fibres(r))
            expected=[]
            for x in range(-30,31):
                y=integer_power_root(evaluate(f,x)**2+k,2)
                if y is not None:expected.extend((x,t) for t in sorted({y,-y}))
            self.assertEqual(r['points'],expected)

    def test_compiler_uses_sturm_for_disjoint_giant_roots(self):
        n=10**100;f=tuple(map(int,P.add(P.power(P.poly([n,-n-1,1]),2),P.ONE)))
        p=compile_constraint(PowerConstraint(f,2));self.assertIn('Sturm',p.method)
        self.assertEqual(p.all_hits(),[(1,[-1,1]),(n,[-1,1])])


class SharpPowerGaps(unittest.TestCase):
    def test_exceptional_residual_fibres_outside_cutoff(self):
        f=[-100,1,0,0,1];b=sharp_bound(f,2);self.assertTrue(verify_bound(b,f,2));self.assertLess(b['bound'],100)
        self.assertEqual(b['exceptional_coordinates'],[100])
        r=ArithmeticEngine().solve(f,strict=True);self.assertEqual(r['points'],[(100,-10000),(100,10000)])
        self.assertTrue(verify_result(r));self.assertEqual(r['proof']['leaf']['exceptional_coordinates_checked'],[100])

    def test_difficult_normalized_quartic(self):
        r=ArithmeticEngine().solve([-199,1,1,1,1],strict=True)
        self.assertEqual(r['points'],[(7,-51),(7,51)]);self.assertEqual(r['statistics']['interval_size'],85)
        self.assertEqual(r['statistics']['candidates_checked'],2);self.assertTrue(verify_result(r))

    def test_all_signs_against_independent_old_finite_bounds(self):
        from perfectpower.core import rigid_certificate
        rng=random.Random(313)
        for d,q in itertools.product((2,3,4,5),(1,2)):
            for _ in range(6):
                base=P.poly([rng.randint(-2,2) for _ in range(q)]+[rng.choice([-1,1]) if d%2 else 1])
                f=tuple(map(int,P.add(P.power(base,d),P.poly([rng.choice([-5,-1,1,5]),rng.randint(-2,2)] if (d-1)*q>1 else [1]))))
                old=rigid_certificate(f,d);r=ArithmeticEngine().solve(f,d,strict=True);expected=[]
                for x in range(-old.cutoff,old.cutoff+1):
                    y=integer_power_root(evaluate(f,x),d)
                    if y is not None:expected.extend((x,t) for t in sorted({y,-y} if d%2==0 else {y}))
                self.assertEqual(r['points'],expected);self.assertTrue(verify_result(r))

    def test_witness_scale_and_integer_center_do_not_inflate_needlessly(self):
        reductions=affine_power_reductions([2,1,0,2,1],2)
        self.assertEqual(reductions[0]['a'],1)
        for reduction in reductions:
            a,b,q,s=(reduction[k] for k in ('a','b','power','witness_scale'));outer=reduction['outer_coefficients']
            for x in range(-5,6):self.assertEqual(s*s*evaluate([2,1,0,2,1],x),evaluate(outer,(a*x+b)**q))

    def test_bound_and_exception_tampering(self):
        f=[-100,1,0,0,1];b=sharp_bound(f,2)
        x=copy.deepcopy(b);x['exceptional_coordinates']=[];self.assertFalse(verify_bound(x,f,2))
        x=copy.deepcopy(b);x['residual_roots']['nodes']=[];self.assertFalse(verify_bound(x,f,2))
        x=copy.deepcopy(b);x['tail_start']=1;x['bound']=0;self.assertFalse(verify_bound(x,f,2))
        with self.assertRaises(WorkLimit):scan_sharp(residue_cover(f,2),b,work_limit=1)

    def test_previous_release_certificates_still_replay(self):
        rows=json.loads((ROOT/'receipts/enhanced_machinery/hard_examples.json').read_text())
        for row in rows['giant_coordinate_examples']:self.assertTrue(verify_result(row))


class DeterminantalMeasures(unittest.TestCase):
    def exhaustive(self,measure,included=(),excluded=()):
        g=measure.graph;zero=g.field.element(0);total=zero;wanted=zero
        for edges,c in g.terms():
            for i in edges:c=c*measure.weights[i]
            total=total+c
            if set(included)<=set(edges) and not set(excluded)&set(edges):wanted=wanted+c
        return wanted*total.inverse()

    def test_all_mixed_events_against_enumeration(self):
        g=ConnectionGraph(2,((0,1,0),(0,1,2),(0,1,1)),4);m=ConnectionMeasure(g,[2,3,5])
        for decisions in itertools.product((-1,0,1),repeat=3):
            included=tuple(i for i,v in enumerate(decisions) if v==1);excluded=tuple(i for i,v in enumerate(decisions) if v==-1)
            self.assertEqual(m.event(included,excluded),self.exhaustive(m,included,excluded))
        self.assertTrue(verify_measure(json.loads(json.dumps(m.receipt()))))

    def test_random_cyclotomic_loops_parallel_and_zero_weight(self):
        rng=random.Random(500)
        for d in (2,3,4,5,6):
            for _ in range(3):
                edges=[(0,1,0),(0,1,1)]+[(rng.randrange(2),rng.randrange(2),rng.randrange(d)) for _ in range(3)]
                m=ConnectionMeasure(ConnectionGraph(2,tuple(edges),d),[1,2,0,3,1])
                self.assertTrue(verify_measure(m.receipt()))
                for i,j in itertools.combinations(range(5),2):
                    self.assertEqual(m.event((i,),(j,)),self.exhaustive(m,(i,),(j,)))
                    self.assertEqual(m.event((i,j)),self.exhaustive(m,(i,j)))

    def test_conditioning_and_basis_size(self):
        g=root_channel_graph([1,1,1,1],4);m=ConnectionMeasure(g);given=m.conditional((0,),(1,))
        values=[g.field.element([Q(x) for x in p]) for p in given['edge_marginals']]
        self.assertEqual(sum(values,g.field.element(0)),g.field.element(2))
        self.assertTrue(verify_conditioning(m.receipt(),given))
        bad=copy.deepcopy(given);bad['edge_marginals'][0]=['0'];self.assertFalse(verify_conditioning(m.receipt(),bad))
        self.assertEqual(ConnectionMeasure.from_receipt(m.receipt()).event((0,),(1,)),m.event((0,),(1,)))
        for i in range(5):
            if i not in (0,1):self.assertEqual(values[i],self.exhaustive(m,(0,i),(1,))*self.exhaustive(m,(0,),(1,)).inverse())
        with self.assertRaises(ValueError):m.conditional((0,1,2))
        with self.assertRaises(ValueError):m.event((0,),(0,))

    def test_rank_deficient_distribution_is_undefined(self):
        m=ConnectionMeasure(ConnectionGraph(3,((0,1,1),(0,1,0)),4))
        self.assertIsNone(m.receipt()['edge_marginals']);self.assertTrue(verify_measure(m.receipt()))
        with self.assertRaises(ValueError):m.event()
        m=ConnectionMeasure(ConnectionGraph(2,((0,1,0),(0,1,1)),4),[1,0])
        self.assertTrue(verify_measure(m.receipt()));self.assertIsNone(m.kernel)

    def test_certificate_tampering_and_budgets(self):
        m=ConnectionMeasure(root_channel_graph([1,2,1],5));r=m.receipt()
        x=copy.deepcopy(r);x['transfer_kernel'][0][0]=['99'];self.assertFalse(verify_measure(x))
        x=copy.deepcopy(r);x['laplacian_inverse'][0][0]=['99'];self.assertFalse(verify_measure(x))
        x=copy.deepcopy(r);x['edge_marginals'][0]=['99'];self.assertFalse(verify_measure(x))
        with self.assertRaises(WorkLimit):ConnectionMeasure(m.graph,work_limit=1)
        with self.assertRaises(ValueError):ConnectionMeasure(m.graph,[-1]*4)
        with self.assertRaises(ValueError):m.event((True,))

    def test_large_graph_has_no_basis_enumeration(self):
        n=10;edges=tuple((i,(i+1)%n,0) for i in range(n))+tuple((i,i,1) for i in range(n))+tuple((i,(i+3)%n,1) for i in range(n))
        m=ConnectionMeasure(ConnectionGraph(n,edges,2));self.assertEqual(m.receipt()['basis_enumerations'],0)
        self.assertTrue(verify_measure(m.receipt()));self.assertEqual(sum((m.kernel[i][i] for i in range(len(edges))),m.field.element(0)),m.field.element(n))
        with self.assertRaises(ValueError):m.graph.terms(subset_limit=100000)

    def test_cli_interfaces(self):
        for args in (['integer-roots','--coeff','[0,0,2,-3,1]'],['square-fibres','--coeff','[2,-3,1]','--k','1'],
                    ['connection-measure','--vertices','2','--edges','[[0,1,0],[0,1,1]]','--power','4','--include','[0]']):
            r=subprocess.run([sys.executable,'-m','perfectpower',*args,'--verify'],capture_output=True,text=True,check=True)
            self.assertTrue(json.loads(r.stdout)['certificate_replay'])


class OperatorAlgebras(unittest.TestCase):
    def test_full_matrix_algebra_and_exact_word_closure(self):
        a=[[[0,1],[0,0]],[[0,0],[1,0]]];r=algebra_profile(a)
        self.assertEqual([r[k]['dimension'] for k in ('algebra','commutant','bicommutant')],[4,1,4]);self.assertTrue(verify_profile(r))
        self.assertTrue(verify_profile(json.loads(json.dumps(r,default=lambda x:str(x)))))

    def test_triangular_gap_has_a_dual_obstruction(self):
        r=algebra_profile([[[1,0],[0,0]],[[0,1],[0,0]]])
        self.assertEqual([r[k]['dimension'] for k in ('algebra','commutant','bicommutant')],[3,1,4])
        self.assertEqual(r['status'],'STRICT_BICOMMUTANT_ENLARGEMENT');self.assertTrue(verify_profile(r))
        self.assertTrue(verify_membership(r['algebra'],r['gap_witness']))

    def test_double_commutant_equality_does_not_imply_semisimplicity(self):
        r=algebra_profile([[[0,1],[0,0]]]);self.assertEqual(r['algebra']['dimension'],2)
        self.assertEqual(r['status'],'DOUBLE_COMMUTANT_CLOSED');self.assertTrue(verify_profile(r))
        operator=r['algebra']['operators'][0]
        self.assertEqual(E.multiply(operator,operator),((Q(0),Q(0)),(Q(0),Q(0))))
        self.assertNotEqual(operator,((Q(0),Q(0)),(Q(0),Q(0))))

    def test_membership_and_unsupported_operator_are_exact(self):
        r=generated_algebra([[[1,0],[0,2]]]);self.assertTrue(verify_algebra(r))
        inside=algebra_membership(r,[[7,0],[0,-9]]);outside=algebra_membership(r,[[0,1],[0,0]])
        self.assertEqual(inside['status'],'IN_GENERATED_ALGEBRA');self.assertEqual(outside['status'],'OUTSIDE_GENERATED_ALGEBRA')
        self.assertTrue(verify_membership(r,inside));self.assertTrue(verify_membership(r,outside))

    def test_transcript_and_commutant_tamper(self):
        r=algebra_profile([[[0,1],[0,0]],[[0,0],[1,0]]])
        x=copy.deepcopy(r);x['algebra']['left_generator_products'][0][0]=(99,)*4;self.assertFalse(verify_profile(x))
        x=copy.deepcopy(r);x['algebra']['basis_words'][-1]=[];self.assertFalse(verify_profile(x))
        x=copy.deepcopy(r);x['commutant']['basis']=[];self.assertFalse(verify_profile(x))
        with self.assertRaises(WorkLimit):generated_algebra(r['algebra']['operators'],product_limit=1)
        with self.assertRaises(ValueError):generated_algebra([[[1.0]]])

    def test_operator_cli(self):
        r=subprocess.run([sys.executable,'-m','perfectpower','operator-algebra','--operators','[[[1,0],[0,0]],[[0,1],[0,0]]]','--verify'],capture_output=True,text=True,check=True)
        output=json.loads(r.stdout);self.assertTrue(output['certificate_replay']);self.assertEqual(output['status'],'STRICT_BICOMMUTANT_ENLARGEMENT')
