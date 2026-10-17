"""Independent operator, scalar, transfer, and exact-tail checks for the bridge."""
import copy
import json
import unittest
from fractions import Fraction as Q
from math import factorial

from perfectpower import raghava_coxeter as R
from perfectpower import e8_lift as lift
from perfectpower import e8_periods as E
from perfectpower.coxeter_mellin import even_pi_coefficient
from perfectpower.period_transport import PhaseObject, even_period_coefficient, primitive_phases


class RaghavaCoxeterTests(unittest.TestCase):
    def test_actual_reflection_operator_and_recurrence(self):
        check = R.reflection_operator_checks()
        self.assertTrue(check['exact_matrix_polynomial_zero'])
        self.assertEqual(check['annihilator'], [1, -8, 14, -7, 1])
        L = R.e8_reflection_operator()
        powers, seq = E.identity(), R.reflection_trace_sequence(80)
        for n in range(81):
            self.assertEqual(sum(powers[i][i] for i in range(8)), seq[n])
            powers = E.matmul(L, powers)
        self.assertEqual(seq[:8], (8,14,42,146,538,2044,7902,30856))

    def test_exact_scalar_bridge_at_all_phases_through_40(self):
        # Source-side finite Bernoulli polynomial at q, versus an independent
        # centered-power expansion of the Raghava moments.  6,560 comparisons.
        count = 0
        for n in range(1,41):
            for q in range(n):
                A = PhaseObject(n, ((q,1),))
                actual = R.mellin_from_moments(R.moment_vector(A,8))
                for k in range(1,9):
                    self.assertEqual(actual[k], even_period_coefficient(A,2*k))
                    count += 1
        self.assertEqual(count,6560)

    def test_triangular_inverse_does_not_need_zeta_independence(self):
        for order in range(17):
            values = tuple(Q((-1)**j*(j*j+3),2*j+1) for j in range(order+1))
            self.assertEqual(R.moments_from_mellin(R.mellin_from_moments(values)), values)
        self.assertEqual(R.bernoulli_bridge_matrix(2), (
            (Q(1),Q(0),Q(0)), (Q(-1,12),Q(1,2),Q(0)),
            (Q(-7,720),Q(1,12),Q(-1,2))))

    def test_faulhaber_transfer_against_explicit_branch_induction(self):
        for n in range(1,13):
            A = PhaseObject(n, ((0,Q(1,3)),(1,Q(-2,5)),(n//2,Q(7,4))))
            for degree in (1,2,3,5,7,11):
                expected = R.moment_vector(R.induce_spectrum(A,degree),6)
                actual = R.apply_matrix(R.induction_moment_matrix(degree,6), R.moment_vector(A,6))
                self.assertEqual(actual,expected)
                matrix = R.induction_moment_matrix(degree,6)
                for j in range(7):
                    for k in range(j+1):
                        centered = sum((Q(2*r-degree+1,2)**(2*(j-k)) for r in range(degree)),Q(0))
                        coefficient = Q(4**(j-k),factorial(2*(j-k))*degree**(2*j))*centered
                        self.assertEqual(matrix[j][k],coefficient)

    def test_transfer_composition_and_mellin_diagonalization(self):
        B=R.bernoulli_bridge_matrix(8)
        for d in (1,2,3,5,11,264):
            A=R.induction_moment_matrix(d,8)
            left=E.matmul(B,A)
            right=tuple(tuple(B[j][k]*(Q(d) if j==0 else Q(1,d**(2*j-1))) for k in range(9)) for j in range(9))
            self.assertEqual(left,right)
            for e in (1,2,3,11,264):
                self.assertEqual(E.matmul(A,R.induction_moment_matrix(e,8)),R.induction_moment_matrix(d*e,8))

    def test_exact_e8_reflection_and_adjoint_moments(self):
        reflection=R.e8_reflection_spectrum()
        adjoint=R.e8_adjoint_spectrum()
        self.assertEqual(R.angle_moment_coefficient(reflection,1),Q(56,45))
        self.assertEqual(R.angle_moment_coefficient(reflection,2),Q(10696,151875))
        self.assertEqual(R.angle_moment_coefficient(adjoint,1),Q(124,3))
        self.assertEqual(R.weight_two_defect(reflection),Q(-4,45))
        self.assertEqual(R.weight_two_defect(adjoint),0)
        for j,z in enumerate(R.mellin_from_moments(R.moment_vector(adjoint,16))[1:],1):
            self.assertEqual(z,even_pi_coefficient('E',8,2*j))
        induced=R.induce_spectrum(adjoint,264)
        self.assertEqual(induced.dimension,65472)
        self.assertEqual(R.angle_moment_coefficient(induced,1),10912)
        self.assertEqual(R.weight_two_defect(induced),0)

    def test_actual_signed_adjoint_operator_matches_the_same_moment_inputs(self):
        T=lift.coxeter_lift()
        Ti=lift.power(T,29)
        L=[]
        for i,(col,invcol) in enumerate(zip(T,Ti)):
            data={i:2}
            for j,c in (*col,*invcol):
                data[j]=data.get(j,0)+c
            L.append(tuple((j,c) for j,c in sorted(data.items()) if c))
        L=tuple(L)
        trace=[E.coxeter_trace(r)+240*(r==0) for r in range(30)]
        coefficients=[1]+[0]*29
        power=lift.identity_map()
        fresh_sequence=R.adjoint_trace_sequence(40)
        for n in range(41):
            actual=sum(dict(col).get(i,0) for i,col in enumerate(power))
            self.assertEqual(actual,sum(a*b for a,b in zip(coefficients,trace)))
            self.assertEqual(actual,fresh_sequence[n])
            coefficients=[2*coefficients[r]+coefficients[(r-1)%30]+coefficients[(r+1)%30] for r in range(30)]
            power=lift.compose(L,power)

    def test_positive_series_encloses_independent_angle_values(self):
        for j in range(1,5):
            previous=None
            for terms in (64,128,256):
                value=R.reflection_partial(j,terms,32)
                self.assertTrue(value['independent_enclosure_overlap'])
                lower,upper=Q(value['lower']),Q(value['upper'])
                target_lower,target_upper=map(Q,value['target_interval'])
                self.assertLessEqual(lower,target_lower)
                self.assertGreaterEqual(upper,target_upper)
                if previous is not None:
                    self.assertGreater(lower,previous[0])
                    self.assertLess(Q(value['tail_absolute']),previous[1])
                previous=(lower,Q(value['tail_absolute']))

    def test_endpoint_deflated_adjoint_series_and_tail(self):
        values=R.adjoint_trace_sequence(512,deflate_trivial=True)
        self.assertEqual(values[0],240)
        self.assertTrue(all(x>=0 for x in values))
        for j in (1,2,3):
            value=R.adjoint_deflated_partial(j,128,32)
            self.assertTrue(value['independent_enclosure_overlap'])
            target_lower,target_upper=map(Q,value['target_interval'])
            self.assertLessEqual(Q(value['lower']),target_lower)
            self.assertGreaterEqual(Q(value['upper']),target_upper)
        self.assertEqual(R.adjoint_deflated_partial(1,32,32)['exact_pi_coefficient'],'112/3')

    def test_fixed_primitive_fiber_obstructs_natural_e8_identification(self):
        obstruction=R.fixed_fiber_obstruction()
        self.assertEqual(obstruction['restricted_terms'],[[1,'240']])
        self.assertFalse(obstruction['equivariant_isomorphism_possible'])
        self.assertEqual(obstruction['primitive_fiber_dimension'],240)

    def test_receipt_and_input_contracts(self):
        evidence=R.receipt(8)
        self.assertEqual(json.loads(json.dumps(evidence)),evidence)
        self.assertEqual(evidence['induction_264']['first_moment_pi_squared_coefficient'],'10912')
        for argument in (-1,True,33):
            with self.assertRaises(ValueError): R.bernoulli_bridge_matrix(argument)
        for argument in (0,-1,True):
            with self.assertRaises(ValueError): R.induction_moment_matrix(argument,4)
        with self.assertRaises(ValueError): R.reflection_partial(0)
        with self.assertRaises(ValueError): R.reflection_partial(1,-1)
        with self.assertRaises(ValueError): R.induce_spectrum(primitive_phases(30),264,branch_budget=100)
        with self.assertRaises(ValueError): R.apply_matrix(((1,2),),(1,))


if __name__=='__main__':
    unittest.main()
