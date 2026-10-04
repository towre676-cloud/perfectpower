import copy
import itertools
import json
import random
import subprocess
import sys
import unittest
from fractions import Fraction as Q
from perfectpower import polyalg as P
from perfectpower import exact_linear as E
from perfectpower.arithmetic_engine import ArithmeticEngine,affine_power_reductions,verify_result
from perfectpower.closest_integer import IntegerLiftOptimizer,verify_optimum
from perfectpower.residue_cover import residue_cover,verify_cover,scan_cover,evaluate
from perfectpower.divisor_square import WorkLimit
from perfectpower.compiler import compile_constraint,PowerConstraint,TriangularConstraint,QuadraticRootConstraint


def expanded(outer,q,a,b):
    f=[0]*(q*(len(outer)-1)+1)
    for i,c in enumerate(outer):f[i*q]=c
    return tuple(map(int,P.compose_linear(P.poly(f),b,a)))


class ResidueCoverTests(unittest.TestCase):
    def test_complete_non_coprime_cover_against_all_residues(self):
        for f,d,moduli in (([1,2,3],2,[8,12,5]),([-3,0,1],3,[4,6,9]),([3,0,0,0,2],2,[16,9])):
            c=residue_cover(f,d,moduli);m=c['modulus'];tables=c['tables']
            expected=[r for r in range(m) if all(evaluate(f,r)%t['modulus'] in {pow(y,d,t['modulus']) for y in range(t['modulus'])} for t in tables)]
            self.assertEqual(list(c['allowed']),expected);self.assertTrue(verify_cover(json.loads(json.dumps(c))))

    def test_negative_closed_intervals_and_repeated_roots(self):
        c=residue_cover([0,0,1],2,[16,9,5])
        result=scan_cover(c,-20,20)
        self.assertEqual(result['points'],[(x,y) for x in range(-20,21) for y in sorted({x,-x})])

    def test_modular_obstruction_is_global(self):
        c=residue_cover([3,0,0,0,2],2)
        self.assertTrue(c['global_obstruction']);self.assertEqual(scan_cover(c,-10**100,10**100)['points'],[])

    def test_budget_and_corruption_fail_closed(self):
        with self.assertRaises(WorkLimit):residue_cover([0,0,1],2,[4096,4095])
        c=residue_cover([0,0,1],2)
        with self.assertRaises(WorkLimit):scan_cover(c,0,100,work_limit=1)
        c['allowed']=[];self.assertFalse(verify_cover(c))
        with self.assertRaises(ValueError):scan_cover(c,0,5)


class StructuralEngineTests(unittest.TestCase):
    def test_giant_shift_degree_12_40_and_odd_power(self):
        n=10**30;e=ArithmeticEngine()
        for outer,q,a,b,d,expected in (([1,1,0,0,1],3,2,-2*n-1,2,[(n,-1),(n,1)]),
                    ([1,-1,0,0,1],10,7,-7*n-1,2,[(n,-1),(n,1)]),([1,1,0,1],5,2,-2*n-1,3,[(n,-1)])):
            r=e.solve(expanded(outer,q,a,b),d,strict=True)
            self.assertEqual(r['points'],expected);self.assertTrue(verify_result(r));self.assertLessEqual(r['statistics']['candidates_checked'],4)

    def test_all_affine_image_conditions_against_outer_enumeration(self):
        outer=[1,1,0,0,1];source=[(-1,-1),(-1,1),(0,-1),(0,1)]
        e=ArithmeticEngine()
        for q,a,b in itertools.product((2,3,4),(1,2,3),range(-3,4)):
            f=expanded(outer,q,a,b);expected=[]
            for x in range(-8,9):
                for u,y in source:
                    if (a*x+b)**q==u:expected.append((x,y))
            r=e.solve(f,strict=True);self.assertEqual(r['points'],sorted(expected));self.assertTrue(verify_result(r))

    def test_rational_center_and_witness_scale(self):
        f=[2,1,0,2,1];reductions=affine_power_reductions(f,2)
        self.assertTrue(any(r['witness_scale']>1 for r in reductions))
        r=ArithmeticEngine().solve(f,strict=True);self.assertTrue(verify_result(r))
        self.assertEqual(r['points'],[(x,y) for x in range(-20,21) for y in range(-500,501) if y*y==evaluate(f,x)])

    def test_positive_negative_zero_run_ge_bounds(self):
        e=ArithmeticEngine()
        for f,d in (([1,1,0,1],3),([1,1,0,-1],3),([1,-1,0,0,0,0,1],2)):
            r=e.solve(f,d,strict=True);self.assertTrue(verify_result(r))
            expected=[]
            from perfectpower.core import integer_power_root
            for x in range(-100,101):
                root=integer_power_root(evaluate(f,x),d)
                if root is not None:expected.extend((x,y) for y in sorted({root,-root} if d%2==0 else {root}))
            self.assertEqual(r['points'],expected)

    def test_generators_and_constant_all_signs(self):
        e=ArithmeticEngine()
        for f,d in (([1,2,1],2),([-1,3,-3,1],3),([0],3),([-8],3),([9],2)):
            r=e.solve(f,d);self.assertEqual(r['status'],'GENERATOR');self.assertTrue(verify_result(r))
        r=e.solve([-1],2);self.assertEqual(r['points'],[]);self.assertTrue(verify_result(r))

    def test_cache_reuse_and_isolation(self):
        e=ArithmeticEngine();a=e.solve(expanded([1,1,0,0,1],2,1,-10));b=e.solve(expanded([1,1,0,0,1],3,1,-20))
        self.assertGreater(e.hits,0);self.assertEqual(e.misses,1)
        a['proof']['leaf']['points']=[]
        c=e.solve(expanded([1,1,0,0,1],2,1,-10));self.assertEqual(c['points'],[(10,-1),(10,1)])
        self.assertTrue(verify_result(c));self.assertFalse(verify_result(a))

    def test_serialized_certificate_and_tamper_detection(self):
        r=ArithmeticEngine().solve(expanded([1,1,0,0,1],3,2,-3));self.assertTrue(verify_result(json.loads(json.dumps(r))))
        for mutate in (lambda a:a['points'].pop(),lambda a:a['proof']['reduction'].__setitem__('b',-4),
                       lambda a:a['proof']['leaf']['cover'].__setitem__('allowed',[]),
                       lambda a:a['proof']['leaf']['bound_certificate'].__setitem__('bound',0),
                       lambda a:a['proof']['leaf'].__setitem__('candidates_checked',0),
                       lambda a:a.__setitem__('execution_verified',True)):
            bad=copy.deepcopy(r);mutate(bad);self.assertFalse(verify_result(bad))

    def test_budget_never_returns_partial_complete(self):
        e=ArithmeticEngine(work_limit=1)
        r=e.solve([1,1,0,1],3);self.assertEqual(r['status'],'UNRESOLVED');self.assertIsNone(r['points'])
        with self.assertRaises(WorkLimit):e.solve([1,1,0,1],3,strict=True)
        for f,d in (([True,0,1],2),([1,0,1],True),([1.0,0,1],2)):
            with self.assertRaises(ValueError):e.solve(f,d)

    def test_unknown_branch_keeps_unresolved_status(self):
        r=ArithmeticEngine().solve([1,1,0,0,2],2)
        self.assertEqual(r['status'],'UNRESOLVED');self.assertFalse(verify_result(r))

    def test_compiler_and_witness_domain_integration(self):
        n=10**30;f=expanded([1,1,0,0,1],3,2,-2*n-1)
        p=compile_constraint(PowerConstraint(f,2));self.assertEqual(p.all_hits(),[(n,[-1,1])]);self.assertEqual(p.count(n-1),0)
        q=compile_constraint(QuadraticRootConstraint(1,0,0,f,'nonneg'));self.assertEqual(q.all_hits(),[(n,[1])])


class ClosestLiftTests(unittest.TestCase):
    def test_all_tied_optima_and_continuous_projection(self):
        r=IntegerLiftOptimizer([[1,1]]).nearest([1],[0,0])
        self.assertEqual(r['minimizers'],[(0,1),(1,0)]);self.assertEqual(r['minimum_energy'],1)
        self.assertEqual(r['continuous_minimum'],Q(1,2));self.assertEqual(r['continuous_point'],(Q(1,2),Q(1,2)));self.assertTrue(verify_optimum(r))

    def test_dense_weighted_lattices_against_independent_boxes(self):
        rng=random.Random(40102026)
        for n in (2,3):
            mass=[[3 if i==j else 1 if abs(i-j)==1 else 0 for j in range(n)] for i in range(n)]
            for _ in range(10):
                a=[[rng.randrange(-3,4) for _ in range(n)]];target=[Q(rng.randrange(-2,3),2) for _ in range(n)]
                r=IntegerLiftOptimizer(a,mass).nearest([0],target)
                candidates=[]
                for v in itertools.product(range(-5,6),repeat=n):
                    if E.apply(a,v)==(0,):
                        delta=tuple(x-y for x,y in zip(v,target));energy=sum(x*y for x,y in zip(delta,E.apply(mass,delta)));candidates.append((energy,v))
                best=min(x[0] for x in candidates);expected=sorted(v for e,v in candidates if e==best)
                self.assertEqual(r['minimum_energy'],best);self.assertEqual(r['minimizers'],expected);self.assertTrue(verify_optimum(r))

    def test_large_coordinate_optimum_and_shared_decomposition(self):
        solver=IntegerLiftOptimizer([[2,3]]);n=10**30
        r=solver.nearest([1],[n,n]);center=Q(n+5,13);lo=center.numerator//center.denominator
        expected=sorted([(-1+3*t,1-2*t) for t in (lo,lo+1)],key=lambda v:sum((x-n)**2 for x in v))[0]
        self.assertEqual(r['minimizers'],[expected]);self.assertTrue(verify_optimum(r));self.assertLess(r['enumeration_nodes'],5)
        solver.nearest([2],[n,n]);self.assertEqual(solver.calls,2)
        exposed=solver.certificate;exposed['rank']=0
        self.assertEqual(solver.nearest([1],[n,n])['minimizers'],[expected])

    def test_dual_obstructions_and_zero_kernel(self):
        for a,b in (([[4,6]],[1]),([[1,0],[0,0]],[0,1])):
            r=IntegerLiftOptimizer(a).nearest(b,[0,0]);self.assertIn('OBSTRUCTION',r['status']);self.assertTrue(verify_optimum(r))
        r=IntegerLiftOptimizer([[1,0],[0,1]]).nearest([3,-2],[0,0]);self.assertEqual(r['minimizers'],[(3,-2)]);self.assertEqual(r['enumeration_nodes'],0);self.assertTrue(verify_optimum(r))

    def test_lll_lattice_equivalence_and_replay(self):
        a=[[1000000,1000001,1]];solver=IntegerLiftOptimizer(a);r=solver.nearest([0],[1,1,1])
        self.assertGreater(len(solver.operations),0);self.assertTrue(verify_optimum(r))
        direct=IntegerLiftOptimizer(a,reduce_basis=False).nearest([0],[1,1,1]);self.assertEqual(r['minimizers'],direct['minimizers'])
        bad=copy.deepcopy(r);bad['proof']['basis_operations'][0][3]+=1;self.assertFalse(verify_optimum(bad))

    def test_serialized_fractional_target_and_metric(self):
        r=IntegerLiftOptimizer([[1,1]],[[Q(3,2),Q(1,2)],[Q(1,2),Q(3,2)]]).nearest([1],[Q(1,3),Q(2,3)])
        raw=json.loads(json.dumps(r,default=lambda v:str(v)));self.assertTrue(verify_optimum(raw))
        raw['minimizers']=[[99,99]];self.assertFalse(verify_optimum(raw))

    def test_budget_exhaustion_and_invalid_geometry(self):
        with self.assertRaises(WorkLimit):IntegerLiftOptimizer([[1,1]],node_limit=1).nearest([1],[0,0])
        with self.assertRaises(WorkLimit):IntegerLiftOptimizer([[0,0]],parameter_limit=1)
        for mass in ([[1,2],[2,1]],[[1.0,0],[0,1]],[[True,0],[0,1]]):
            with self.assertRaises(ValueError):IntegerLiftOptimizer([[1,1]],mass)


class EnhancedCLITests(unittest.TestCase):
    def test_both_commands_verify_their_certificates(self):
        for args in (['exact-solve','--coeff','[1,1,0,1]','--d','3','--verify'],
                     ['nearest-lift','--matrix','[[1,1]]','--rhs','[1]','--target','[0,0]','--verify']):
            p=subprocess.run([sys.executable,'-m','perfectpower',*args],check=True,capture_output=True,text=True)
            self.assertTrue(json.loads(p.stdout)['certificate_replay'])


if __name__=='__main__':unittest.main()
