import random
import unittest

from perfectpower.divisor_square import analyse, solve, WorkLimit


class SolutionChartTests(unittest.TestCase):
    def test_multiple_points_per_parameter(self):
        r = analyse([-1, 0, 1], 1)
        self.assertEqual(r['parameters'], [(0, -1), (0, 1)])
        self.assertEqual(r['known_cardinality'], 4)
        self.assertEqual([f['cardinality'] for f in r['fibres']], [2, 2])
        self.assertTrue(r['complete'])

    def test_repeated_root_counted_once(self):
        r = analyse([4, -4, 1], 1)
        self.assertEqual(r['known_points'], [(2, -1), (2, 1)])

    def test_empty_fibres_are_closed(self):
        r = analyse([1, 0, 1], 1)
        self.assertEqual(r['known_points'], [])
        self.assertTrue(r['complete'])
        self.assertEqual(len(r['solved_parameters']), 2)

    def test_unresolved_is_not_empty_complete(self):
        r = analyse([1_000_000, 1], 1, fibre_work_limit=10)
        self.assertEqual(r['known_points'], [])
        self.assertFalse(r['complete'])
        self.assertEqual(r['status'], 'PARTIAL')
        self.assertEqual(r['residual_parameters'], [(0, -1), (0, 1)])
        self.assertFalse(r['execution_verified'])

    def test_coverage_failure_raises(self):
        with self.assertRaises(WorkLimit):
            analyse([0, 1], 101, parameter_work_limit=2)

    def test_mixed_closed_and_residual(self):
        r = analyse([2, 1], 9, fibre_work_limit=1)
        self.assertTrue(r['solved_parameters'])
        self.assertTrue(r['residual_parameters'])
        self.assertEqual(set(r['parameters']),
                         set(r['solved_parameters']) | set(r['residual_parameters']))
        self.assertEqual(sum(f['cardinality'] for f in r['fibres']),
                         r['known_cardinality'])

    def test_full_matches_complete_solver(self):
        rng = random.Random(903)
        for _ in range(100):
            coefficients = [rng.randint(-10, 10) for _ in range(rng.randint(2, 6))]
            coefficients[-1] = rng.choice([-3, -2, -1, 1, 2, 3])
            k = rng.choice([i for i in range(-20, 21) if i])
            r = analyse(coefficients, k)
            self.assertEqual(r['known_points'], solve(coefficients, k)['points'])
            self.assertTrue(r['complete'])

    def test_input_limits(self):
        for kwargs in ({'fibre_work_limit': 0}, {'parameter_work_limit': 0}):
            with self.assertRaises(ValueError):
                analyse([0, 1], 1, **kwargs)


if __name__ == '__main__':
    unittest.main()
