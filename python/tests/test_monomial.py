import itertools
import random
import unittest
from fractions import Fraction as Q
from perfectpower.monomial import (solve_monomial,solve_rational_monomial,coercive_weights,
    eliminate_exponents,recovered_2025_packet,OLD_MATRIX,MonomialLimit)
from perfectpower.integral_lattice import smith_invariants
from perfectpower.exact_linear import apply,inverse,multiply
from perfectpower.monomial_projection import project_monomial_query


def product(point,row):
    out=Q(1)
    for x,e in zip(point,row):out*=Q(x)**e
    return out


class MonomialTests(unittest.TestCase):
    def test_historical_torsion_correction_and_two_eliminations(self):
        r=recovered_2025_packet()
        self.assertEqual(r['smith_certificate']['smith_factors'],[1,1,1,3])
        self.assertEqual(smith_invariants(OLD_MATRIX)['smith_factors'],[1,1,1,3])
        self.assertEqual(len(r['integer_kernel']['kernel_basis']),5)
        self.assertEqual(r['historical_consequences'][0]['exponents'],[36,0,-24,-1,9,0,0,0,0])
        self.assertEqual(r['historical_consequences'][1]['exponents'],[0,0,0,-5,0,0,-24,150,-30])
        relations=r['hidden_variable_elimination']['relations']
        self.assertEqual(len(relations),2)
        for relation in relations:self.assertEqual([relation['exponents'][j] for j in (1,5)],[0,0])
        self.assertFalse(r['hidden_variable_elimination']['projection_complete'])

    def test_cube_compatibility_witness_and_rational_fibre(self):
        bad=solve_rational_monomial(OLD_MATRIX,[1,1,2,1])
        self.assertEqual(bad['status'],'RATIONAL_MONOMIAL_PRIME_OBSTRUCTION')
        self.assertEqual(bad['prime'],2);self.assertEqual(bad['obstruction']['modulus'],3)
        good=solve_rational_monomial(OLD_MATRIX,[1,1,8,1])
        self.assertEqual(good['status'],'RATIONAL_MONOMIAL_FIBRE');self.assertEqual(good['parameter_count'],5)
        for parameters in ((Q(1),)*5,(Q(2),Q(3,2),Q(5),Q(1,7),Q(11))):
            point=[Q(x)*product(parameters,[v[i] for v in good['parameter_exponents']])
                   for i,x in enumerate(good['particular'])]
            self.assertEqual([product(point,row) for row in OLD_MATRIX],[1,1,8,1])

    def test_rational_fibre_parameter_completeness_on_constructed_points(self):
        rng=random.Random(20250817)
        for _ in range(50):
            a=[[rng.randrange(-3,4) for j in range(3)] for i in range(2)]
            source=[Q(rng.randrange(1,10),rng.randrange(1,10)) for j in range(3)]
            rhs=[product(source,row) for row in a]
            result=solve_rational_monomial(a,rhs);self.assertEqual(result['status'],'RATIONAL_MONOMIAL_FIBRE')
            particular=list(map(Q,result['particular']));iv=inverse(result['certificate']['right']);r=result['certificate']['rank']
            # Exact exponents of ratio at a finite covering set of primes.
            for p in (2,3,5,7):
                def val(q):
                    n,d=q.numerator,q.denominator;v=0
                    while n%p==0:n//=p;v+=1
                    while d%p==0:d//=p;v-=1
                    return v
                difference=[val(x/y) for x,y in zip(source,particular)];coords=apply(iv,difference)
                self.assertFalse(any(coords[:r]));self.assertTrue(all(x.denominator==1 for x in coords))
                self.assertEqual([sum(int(coords[r+j])*v[i] for j,v in enumerate(result['parameter_exponents'])) for i in range(3)],difference)

    def test_positive_finite_product_and_square_cube_constraint(self):
        self.assertEqual(solve_monomial([[1,1]],[12])['points'],[[1,12],[2,6],[3,4],[4,3],[6,2],[12,1]])
        r=solve_monomial([[2,3]],[2**20*3**12]);self.assertEqual(len(r['points']),12)
        self.assertTrue(all(x*x*y**3==2**20*3**12 for x,y in r['points']))
        self.assertEqual([len(c['profiles']) for c in r['valuation_profiles']],[4,3])

    def test_signed_exponents_and_automatic_coercive_combinations(self):
        a=[[2,-3],[1,1]];b=[Q(4,27),6]
        self.assertEqual(solve_monomial(a,b,weights=[0,1])['points'],[[2,3]])
        self.assertEqual(solve_monomial(a,b)['points'],[[2,3]])
        # Automatic fallback chooses an exact rational solution A^t*w=1.
        w,c=coercive_weights([[1,-1],[0,1]])
        self.assertEqual(c,[1,1]);self.assertEqual(w,[1,2])

    def test_empty_reason_boundaries(self):
        self.assertEqual(solve_monomial([[2]],[12])['status'],'EMPTY_POWER_PRODUCT')
        self.assertEqual(solve_monomial([[1]],[Q(1,2)])['status'],'EMPTY_NONINTEGRAL_PRODUCT')
        self.assertEqual(solve_monomial([[1,1],[1,1]],[2,3],weights=[1,0])['status'],'EMPTY_PRIME_SUPPORT_OBSTRUCTION')
        # Integral valuation coordinates exist, but are negative.
        self.assertEqual(solve_monomial([[1,-1],[0,1]],[Q(1,2),1])['points'],[])
        self.assertEqual(solve_monomial([[2,3]],[2])['status'],'EMPTY_NONNEGATIVE_VALUATION_FIBRE')
        self.assertEqual(solve_monomial([[1,1]],[1])['points'],[[1,1]])

    def test_independent_brute_force_all_small_positive_solutions(self):
        for a in ([[1,1]],[[2,1]],[[1,2],[1,1]],[[1,-1],[0,1]],[[2,-1],[1,1]]):
            for sample in itertools.product(range(1,6),repeat=2):
                rhs=[product(sample,row) for row in a]
                result=solve_monomial(a,rhs)
                bound=max(sample)**3
                expected=sorted([list(point) for point in itertools.product(range(1,bound+1),repeat=2)
                                 if all(product(point,row)==b for row,b in zip(a,rhs))])
                self.assertEqual(result['points'],expected)

    def test_huge_exact_power_fast_path_and_huge_exponent_rejection(self):
        n=10**100+37
        result=solve_monomial([[3]],[n**3])
        self.assertEqual(result['points'],[[n]]);self.assertEqual(result['method'],'exact positive power root')
        self.assertEqual(solve_monomial([[10**100]],[2])['points'],[])
        self.assertEqual(solve_monomial([[1],[1]],[2,3],weights=[1,0])['status'],'EMPTY_FIXED_POINT_CONFLICT')
        self.assertEqual(solve_monomial([[2,2]],[2])['status'],'EMPTY_VALUATION_OBSTRUCTION')

    def test_elimination_is_consequence_not_integer_projection(self):
        # x^2=y implies y is a square; eliminating x gives no row-combination
        # constraint, but does not mean every y can lift to an integer x.
        r=eliminate_exponents([[2,-1]],[0]);self.assertEqual(r['relations'],[])
        self.assertFalse(r['projection_complete'])
        # xy=xz does not permit cancelling x=0. The returned relation names
        # its nonzero domain explicitly rather than claiming zero fibres.
        r=eliminate_exponents([[0,1,-1]],[0]);self.assertIn('nonzero',r['domain'])
        with self.assertRaises(ValueError):eliminate_exponents([[1,1]],[0,0])

    def test_invalid_inputs_and_fail_closed_resource_budgets(self):
        for a,b in [([[True]],[1]),([[1.0]],[1]),([[1]],[0]),([[1]],[1.1]),([[1]],[True])]:
            with self.assertRaises(ValueError):solve_monomial(a,b)
        with self.assertRaises(ValueError):solve_monomial([[1,-1]],[2])
        with self.assertRaises(ValueError):solve_monomial([[1,1]],[2],weights=[-1])
        with self.assertRaises(MonomialLimit):solve_monomial([[1,1]],[12],point_limit=5)
        with self.assertRaises(MonomialLimit):solve_monomial([[1,1]],[1000003],work_limit=2)
        with self.assertRaises(MonomialLimit):solve_rational_monomial([[1]],[1000003],work_limit=2)
        with self.assertRaises(MonomialLimit):solve_monomial([[1]],[2**100],bit_limit=20)


class MonomialProjectionTests(unittest.TestCase):
    @staticmethod
    def script(body,names=('x','y','z')):
        return '(set-logic QF_NIA)\n'+''.join(f'(declare-const {n} Int)\n' for n in names)+body+'\n(check-sat)\n'

    def test_projection_keeps_unrestricted_residual_variables(self):
        source=self.script('(assert (> x 0))(assert (> y 0))(assert (= (* x y) 12))(assert (= z (* x y)))')
        r=project_monomial_query(source)
        self.assertEqual(r.eliminated_symbols,('x','y'));self.assertEqual(r.remaining_symbols,('z',))
        self.assertEqual(len(r.points),6);self.assertTrue(r.linear)
        self.assertIn('(= z 12)',r.smt)

    def test_empty_result_and_nonlinear_residual(self):
        r=project_monomial_query(self.script('(assert (> x 0))(assert (> y 0))(assert (= (* x x y y y) 2))(assert (= z (* x y)))'))
        self.assertIn('(assert false)',r.smt);self.assertTrue(r.linear)
        r=project_monomial_query(self.script('(assert (> x 0))(assert (> y 0))(assert (= (* x y) 12))(assert (= (* z z) x))'))
        self.assertFalse(r.linear);self.assertIn('(set-logic QF_NIA)',r.smt)

    def test_positive_domain_or_disjunction_cannot_be_invented(self):
        for body in ('(assert (= (* x y) 12))',
                     '(assert (or (> x 0) (< x 0)))(assert (> y 0))(assert (= (* x y) 12))',
                     '(assert (> x 0))(assert (> y 0))(assert (or (= (* x y) 12) (= (* x y) 13)))'):
            with self.assertRaises(ValueError):project_monomial_query(self.script(body))
        with self.assertRaises(MonomialLimit):project_monomial_query(self.script('(assert (> x 0))(assert (> y 0))(assert (= (* x y) 12))'),point_limit=5)

    def test_z3_original_projected_and_independent_residual_models(self):
        try:import z3
        except ImportError:self.skipTest('optional z3 unavailable')
        cases=[('(assert (= z (* x y)))','sat'),('(assert (= z (* x y)))(assert (> z 12))','unsat'),
               ('(assert (= (* z z) x))(assert (> z 1))','sat')]
        for residual,expected in cases:
            source=self.script('(assert (> x 0))(assert (> y 0))(assert (= (* x y) 12))'+residual)
            r=project_monomial_query(source)
            original,projected=z3.Solver(),z3.Solver()
            original.add(z3.parse_smt2_string(source));projected.add(z3.parse_smt2_string(r.smt))
            self.assertEqual(str(original.check()),expected);self.assertEqual(str(projected.check()),expected)
            if expected=='sat':
                model=projected.model();zvalue=model.eval(z3.Int('z'),model_completion=True).as_long()
                matched=False
                for x,y in r.points:
                    original.push();original.add(z3.Int('x')==x,z3.Int('y')==y,z3.Int('z')==zvalue)
                    matched |= original.check()==z3.sat;original.pop()
                self.assertTrue(matched)

if __name__=='__main__':unittest.main()
