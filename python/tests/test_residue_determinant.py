import copy
import unittest
from perfectpower.residue_determinant import (
    adjugate, auxiliary_packet, determinant, determinant_packet, kernel_packet,
    monomial_matrix, multiply, native_auxiliary, native_determinant,
    native_kernel, verify_auxiliary, verify_determinant, verify_kernel)


class ResidueDeterminantTests(unittest.TestCase):
    def test_fraction_free_pivoting_and_adjugate(self):
        a = [[0, 2, 1], [1, 0, 3], [4, 1, 0]]
        self.assertEqual(determinant(a), 25)
        self.assertEqual(multiply(a, adjugate(a)), [[25, 0, 0], [0, 25, 0], [0, 0, 25]])
        self.assertEqual(determinant([[3]]), 3)
        self.assertEqual(adjugate([[3]]), [[1]])

    def test_rectangular_kernel_and_rank_extremes(self):
        for a, rank in [([[1, 2, 3], [2, 4, 6]], 1), ([[0, 0, 0]], 0),
                        ([[1, 0], [0, 1]], 2), ([[1, 1], [0, 1], [1, 2]], 2)]:
            packet = kernel_packet(a)
            self.assertTrue(verify_kernel(packet))
            self.assertEqual(packet['rank'], rank)
            self.assertEqual(len(packet['relations']) == 0, rank == len(a[0]))

    def test_integral_index_gap_is_not_promoted(self):
        packet = kernel_packet([[1, 1, 1]])
        self.assertEqual(packet['kernel_matrix'], [[2, -1, -1], [-1, 2, -1], [-1, -1, 2]])
        self.assertFalse(packet['integral_saturation_certified'])
        # Every image column combination has all three coordinates equal mod 3.
        self.assertTrue(all(len({x % 3 for x in c}) == 1 for c in packet['relations']))
        self.assertNotEqual(1 % 3, (-1) % 3)  # (1,-1,0) is a missing integral kernel vector.

    def test_tampered_kernel_witnesses(self):
        packet = kernel_packet([[1, 2, 3], [2, 4, 6]])
        for field, value in [('rank', 2), ('gram_determinant', 15),
                             ('independent_row_indices', []), ('integral_saturation_certified', True),
                             ('relations', [[1, 0, 0]]), ('execution_verified', True)]:
            bad = copy.deepcopy(packet); bad[field] = value
            self.assertFalse(verify_kernel(bad), field)

    def test_source_bound_parabola(self):
        packet = auxiliary_packet([[0, 0], [1, 1], [2, 4], [3, 9]],
                                  [[0, 0], [1, 0], [0, 1], [2, 0]])
        self.assertTrue(verify_auxiliary(packet))
        self.assertIn([0, 0, 1, -1], packet['kernel']['relations'])
        self.assertIn('evaluation_source', native_auxiliary(packet))
        bad = copy.deepcopy(packet); bad['points'][-1][1] = 10
        self.assertFalse(verify_auxiliary(bad))
        bad = copy.deepcopy(packet); bad['exponents'][2] = [0, 2]
        self.assertFalse(verify_auxiliary(bad))
        bad = copy.deepcopy(packet); bad['global_completeness'] = True
        self.assertFalse(verify_auxiliary(bad))

    def test_centered_monomials(self):
        a, center = monomial_matrix([[3, -2], [4, 1]], [[0, 0], [1, 1]], [3, -2])
        self.assertEqual(a, [[1, 0], [1, 3]])
        self.assertEqual(center, [3, -2])

    def test_modular_bound_certifies_zero(self):
        packet = determinant_packet([[1, 2, 3], [2, 3, 4], [3, 4, 5]], 1009)
        self.assertEqual(packet['status'], 'zero-certified')
        self.assertEqual(packet['determinant_bound'], 360)
        self.assertEqual(packet['divisor'], 1009)
        self.assertTrue(verify_determinant(packet))
        self.assertIn('determinant_dvd_of_transform', native_determinant(packet))

    def test_multiple_divisible_rows(self):
        packet = determinant_packet([[1, 2, 3], [2, 4, 6], [3, 6, 9]], 101)
        self.assertEqual(packet['divisor'], 101**2)
        self.assertTrue(verify_determinant(packet))
        self.assertEqual(packet['status'], 'zero-certified')

    def test_insufficient_bound_is_unresolved(self):
        packet = determinant_packet([[3, 0], [0, 1]], 3)
        self.assertTrue(verify_determinant(packet))
        self.assertEqual(packet['status'], 'bound-insufficient')
        self.assertEqual(determinant(packet['matrix']), 3)
        with self.assertRaises(ValueError): native_determinant(packet)
        bad = copy.deepcopy(packet); bad['status'] = 'zero-certified'
        self.assertFalse(verify_determinant(bad))

    def test_composite_unit_pivots_and_rejection(self):
        self.assertTrue(verify_determinant(determinant_packet([[1, 2], [2, 4]], 35)))
        with self.assertRaises(ValueError): determinant_packet([[2, 0], [0, 1]], 4)

    def test_tampered_divisibility_coprimality_and_bound(self):
        packet = determinant_packet([[1, 2, 3], [2, 3, 4], [3, 4, 5]], 1009)
        for field, value in [('modulus', 3), ('divisor', 1009**2), ('row_bounds', [0, 4, 5]),
                             ('determinant_bound', 0), ('row_weights', [1, 1, 1]),
                             ('execution_verified', True)]:
            bad = copy.deepcopy(packet); bad[field] = value
            self.assertFalse(verify_determinant(bad), field)
        bad = copy.deepcopy(packet); bad['transform'][0][0] += 1
        self.assertFalse(verify_determinant(bad))
        bad = copy.deepcopy(packet); bad['transformed'][-1][0] += 1
        self.assertFalse(verify_determinant(bad))

    def test_shapes_duplicates_and_literal_budgets(self):
        for a in [[], [[True]], [[1], [1, 2]], [[2**4097]]]:
            with self.assertRaises(ValueError): kernel_packet(a)
        with self.assertRaises(ValueError): auxiliary_packet([[1]], [[1], [1]])
        with self.assertRaises(ValueError): auxiliary_packet([[1]], [[13]])
        with self.assertRaises(ValueError): native_kernel(kernel_packet([[1, 2]]*9))
        with self.assertRaises(ValueError): native_kernel(kernel_packet([[int(i == j) for j in range(5)] for i in range(5)]))

    def test_nonunit_transform_is_rejected(self):
        packet = determinant_packet([[1, 1], [1, 1]], 101)
        packet['transform'] = [[101, 0], [0, 101]]
        packet['transformed'] = [[101, 101], [101, 101]]
        packet['row_weights'] = [1, 1]
        packet['divisor'] = 101**2
        self.assertFalse(verify_determinant(packet))

    def test_json_service_operations(self):
        from perfectpower.query_service import dispatch
        c = None
        packet = dispatch(c, {'op': 'integral_kernel_packet', 'args': {'a': [[1, 1, 1]]}})
        self.assertTrue(dispatch(c, {'op': 'verify_integral_kernel', 'args': {'packet': packet}})['valid'])
        self.assertIn('lean_source', dispatch(c, {'op': 'native_integral_kernel', 'args': {'packet': packet}}))
        a = dispatch(c, {'op': 'bounded_auxiliary_packet', 'args': {
            'points': [[0, 0], [1, 1], [2, 4]], 'exponents': [[0, 1], [2, 0]]}})
        self.assertTrue(dispatch(c, {'op': 'verify_bounded_auxiliary', 'args': {'packet': a}})['valid'])
        self.assertIn('evaluation_source', dispatch(c, {'op': 'native_bounded_auxiliary', 'args': {'packet': a}})['lean_source'])
        d = dispatch(c, {'op': 'residue_determinant_packet', 'args': {'a': [[1, 1], [1, 1]], 'modulus': 101}})
        self.assertTrue(dispatch(c, {'op': 'verify_residue_determinant', 'args': {'packet': d}})['valid'])
        self.assertIn('determinant_zero', dispatch(c, {'op': 'native_residue_determinant', 'args': {'packet': d}})['lean_source'])


if __name__ == '__main__':
    unittest.main()
