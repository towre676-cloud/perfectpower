"""Published specializations, independent polynomial checks and analytic tails."""
import copy
import json
import math
import unittest
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from itertools import combinations
from perfectpower.raghava_periods import (
    sine_pole, verify_sine_pole, evaluate_sine_pole, harmonic_factors,
    arcsine_kernel_coefficients, arcsine_kernel, arcsine_moment, arcsine_angle,
    two_order_cancellation, verify_two_order, cancellation_partial, verify_receipt,
)


class RaghavaPeriodsTests(unittest.TestCase):
    def test_original_seven_published_sine_examples(self):
        # Independent published e-polynomial transcriptions, powers of e^-1.
        expected = [
            {1: Q(1)}, {2: Q(1)}, {3: Q(9, 8), 1: Q(-3, 8)},
            {4: Q(4, 3), 2: Q(-2, 3)},
            {5: Q(625, 384), 3: Q(-405, 384), 1: Q(10, 384)},
            {6: Q(81, 40), 4: Q(-64, 40), 2: Q(5, 40)},
            {7: Q(7*16807, 46080), 5: Q(-7*15625, 46080),
             3: Q(7*2187, 46080), 1: Q(-35, 46080)},
        ]
        for k, coefficients in enumerate(expected, 1):
            receipt = sine_pole(k)
            actual = {row['exp_power']: Q(row['coefficient']) for row in receipt['terms']}
            self.assertEqual(actual, coefficients)
            self.assertEqual(receipt['convergence'], 'CONDITIONAL_IMPROPER' if k == 1 else 'ABSOLUTE')
            self.assertTrue(verify_sine_pole(json.loads(json.dumps(receipt))))

    def test_sine_parameters_scaling_and_tamper(self):
        # x=y/a gives a^(k-1)*I_k(1,a*b), independent of the residue expansion.
        for k in (1, 2, 5, 12):
            scaled = sine_pole(k, '3/2', '2/5')
            base = sine_pole(k, 1, '3/5')
            self.assertAlmostEqual(evaluate_sine_pole(scaled)['value'],
                                   float(Q(3, 2)**(k-1))*evaluate_sine_pole(base)['value'], places=10)
        changed = copy.deepcopy(scaled)
        changed['terms'][0]['coefficient'] = '0'
        self.assertFalse(verify_sine_pole(changed))

    def test_symmetric_recurrence_against_explicit_subsets(self):
        for n in range(1, 9):
            actual = harmonic_factors(n, 4)
            for r in range(5):
                expected = sum((math.prod((Q(1, j*j) for j in subset), start=Q(1))
                                for subset in combinations(range(1, n), r)), Q(0))
                self.assertEqual(actual[r], expected)

    def test_kernel_recurrence_satisfies_differential_equation(self):
        # Direct coefficient identity for (4-t²)y''-t*y'+4u²*y=0.
        for u in (Q(0), Q(1, 3), Q(-5, 2), Q(7)):
            values = arcsine_kernel_coefficients(u, 18)
            for n in range(18):
                self.assertEqual(4*(2*n+2)*(2*n+1)*values[n+1]
                                 +(4*u*u-4*n*n)*values[n], 0)
        complete = arcsine_kernel(3, '3/2', 3)
        self.assertEqual(Q(complete['tail_absolute']), 0)
        # cos(6asin(t/2)) = 1-9t²/2+3t⁴-t⁶/2.
        t = Q(3, 2)
        self.assertEqual(Q(complete['partial']), 1-Q(9, 2)*t*t+3*t**4-Q(1, 2)*t**6)

    def test_real_arcsine_moments_and_rational_bounds(self):
        for j, t, terms in ((1, Q(1), 28), (3, Q(-3, 2), 48), (2, Q(19, 10), 80)):
            receipt = arcsine_moment(j, t, terms)
            target = 4**j/math.factorial(2*j)*math.asin(float(t)/2)**(2*j)
            lower, upper = float(Q(receipt['lower'])), float(Q(receipt['upper']))
            self.assertLessEqual(lower-1e-15, target)
            self.assertGreaterEqual(upper+1e-15, target)
            self.assertGreaterEqual(Q(receipt['tail_absolute']), 0)
            self.assertTrue(verify_receipt(json.loads(json.dumps(receipt))))
        receipt = arcsine_kernel('2/3', '3/2', 48)
        value = math.cos(Q(4, 3)*math.asin(.75))
        self.assertLessEqual(float(Q(receipt['lower']))-1e-15, value)
        self.assertGreaterEqual(float(Q(receipt['upper']))+1e-15, value)
        self.assertTrue(verify_receipt(receipt))
        receipt['tail_absolute'] = '0'
        self.assertFalse(verify_receipt(receipt))
        angle = arcsine_angle(1, '1/840')
        self.assertEqual(angle['exact'], dict(coefficient='1/352800', pi_power=2))
        self.assertTrue(verify_receipt(angle))
        refined = arcsine_angle(1, '1/221760')
        self.assertEqual(Q(angle['exact']['coefficient'])/Q(refined['exact']['coefficient']), 264**2)

    def test_two_order_weight_seven_matches_primary_source(self):
        receipt = two_order_cancellation(2, 3)
        self.assertEqual((receipt['A'], receipt['D']), (296, 256))
        self.assertEqual(receipt['harmonic_coefficients'], [
            dict(e_index=1, pi_power=2, coefficient='-1/180'),
            dict(e_index=2, pi_power=0, coefficient='1')])
        self.assertEqual(receipt['zeta_coefficients'], [
            dict(zeta_order=3, pi_power=4, coefficient='61/3645'),
            dict(zeta_order=5, pi_power=2, coefficient='-20153/9720'),
            dict(zeta_order=7, pi_power=0, coefficient='24563/1296')])
        self.assertTrue(verify_two_order(json.loads(json.dumps(receipt))))
        receipt['zeta_coefficients'][0]['coefficient'] = '0'
        self.assertFalse(verify_two_order(receipt))

    def test_every_supported_pair_cancels_all_sine_orders(self):
        for s in range(2, 17):
            for r in range(1, s):
                receipt = two_order_cancellation(r, s)
                self.assertEqual(Q(receipt['polynomial']['coefficients'][1]), 0)
                self.assertTrue(all(Q(jet['product']) == 0 for jet in receipt['cancellation_jets']))
                selected = [jet['order']//2 for jet in receipt['cancellation_jets']
                            if Q(jet['endpoint_even_derivative_scaled'])]
                self.assertEqual(selected, [r, s])

    def test_independent_high_precision_sum_integral_zeta_and_tail(self):
        # Euler's transformation of eta(s) is independent of the arcsine
        # recurrence. This high precision check needs only the standard library.
        with localcontext() as context:
            context.prec = 180
            dpi = Decimal('3.1415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679')
            def decimal(value):
                value = Q(value)
                return Decimal(value.numerator)/value.denominator
            def zeta(order):
                differences = [Decimal(1)/Decimal(k+1)**order for k in range(280)]
                eta = Decimal(0)
                denominator = Decimal(2)
                while differences:
                    eta += differences[0]/denominator
                    differences = [a-b for a, b in zip(differences, differences[1:])]
                    denominator *= 2
                return eta/(1-Decimal(2)**(1-order))
            zetas = {order: zeta(order) for order in (3, 5, 7, 9, 11)}
            for r, s in ((1, 2), (2, 3), (1, 4), (3, 5)):
                receipt = two_order_cancellation(r, s)
                partial = cancellation_partial(receipt, 80)
                self.assertTrue(verify_receipt(json.loads(json.dumps(partial))))
                lhs = sum(decimal(row['coefficient'])*dpi**row['pi_power']
                          for row in partial['pi_coefficients'])
                rhs = sum(decimal(row['coefficient'])*dpi**row['pi_power']*zetas[row['zeta_order']]
                          for row in receipt['zeta_coefficients'])
                self.assertLess(abs(lhs-rhs), decimal(partial['tail_absolute']))
        try:
            import mpmath as mp
        except ImportError:
            return  # Optional quadrature below; Decimal checks above always run.
        with mp.workdps(75):
            def number(value):
                value = Q(value)
                return mp.mpf(value.numerator)/value.denominator
            for r, s in ((1, 2), (2, 3), (1, 4), (3, 5)):
                receipt = two_order_cancellation(r, s)
                partial = cancellation_partial(receipt, 80)
                lhs = sum(number(row['coefficient'])*mp.pi**row['pi_power']
                          for row in partial['pi_coefficients'])
                rhs = sum(number(row['coefficient'])*mp.pi**row['pi_power']*mp.zeta(row['zeta_order'])
                          for row in receipt['zeta_coefficients'])
                self.assertLess(abs(lhs-rhs), number(partial['tail_absolute']))
                # Numerical integration uses the polynomial/log kernel, separate
                # from the harmonic recurrence and Fourier-zeta output.
                alpha = mp.pi/6
                coefficients = [number(c) for c in receipt['polynomial']['coefficients']]
                def integrand(theta):
                    v = theta/alpha
                    P = alpha**(2*s-1)*mp.polyval(list(reversed(coefficients)), v)
                    sin = mp.sin(theta)
                    return P*(-(receipt['A']+1)*mp.log(1-2*sin)
                              -receipt['A']*mp.log(1+2*sin)+receipt['D']*mp.log(2*sin))
                integral = mp.quad(integrand, [0, alpha/2, alpha])
                normalized = 4**s/mp.factorial(2*s-1)*integral
                self.assertLess(abs(normalized-rhs), mp.mpf('1e-65'))

    def test_domain_rejections_and_finite_work_limits(self):
        for args in ((0,), (2, 0), (2, 1, -1), (True,)):
            with self.assertRaises(ValueError):
                sine_pole(*args)
        for function, args in ((arcsine_moment, (1, 2)), (arcsine_kernel, (1, -2)),
                               (two_order_cancellation, (2, 2)),
                               (two_order_cancellation, (1, 17)),
                               (arcsine_kernel_coefficients, (1, 4097))):
            with self.assertRaises(ValueError):
                function(*args)


if __name__ == '__main__':
    unittest.main()
