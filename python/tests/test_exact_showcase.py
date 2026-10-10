"""Integration against enumeration, matrix dynamics and exact independent sums."""
import unittest
import json
from fractions import Fraction as Q
from perfectpower.exact_showcase import query, oracle, machine, build_results, four_count, four_rank
from perfectpower.cost_resolvents import verify_cost_quotient
from perfectpower.catalogue import encoded


class ExactShowcaseTests(unittest.TestCase):
    def test_four_coordinate_oracle_against_enumeration(self):
        for budget in range(18):
            points = [[x, y, u, (budget-x-2*y-u)//2]
                      for x in range(budget+1) for y in range((budget-x)//2+1)
                      for u in range(budget-x-2*y+1) if (budget-x-2*y-u) % 2 == 0]
            self.assertEqual(four_count(budget), len(points))
            for rank, point in enumerate(points):
                self.assertEqual(four_rank(budget, point), rank)

    def test_all_small_restricted_populations_and_objective_ties(self):
        for filtered in (False, True):
            for budget in range(45):
                points = [[x, (budget-x)//2] for x in range(budget+1)
                          if (budget-x) % 2 == 0 and
                          (not filtered or x % 3 == 1 and ((budget-x)//2) % 5 == 2)]
                self.assertEqual(oracle(budget, filtered)['count'], len(points))
                for rank in ({0, len(points)//2, len(points)-1} if points else set()):
                    for objective in ((3, 5), (1, 3), (1, 2), (-3, -5), (0, 0)):
                        actual = query(budget, rank, objective, filtered)
                        scores = [sum(a*b for a, b in zip(objective, p)) for p in points]
                        maximum = max(scores)
                        self.assertEqual(list(map(int, actual['point'])), points[rank])
                        self.assertEqual(int(actual['maximum']), maximum)
                        self.assertEqual(int(actual['maximizer_count']), scores.count(maximum))
                        self.assertEqual(int(actual['reverse_rank']), rank)

    def test_large_restriction_and_domain(self):
        for budget in (10**12, 2**64-1):
            for filtered in (False, True):
                count = oracle(budget, filtered)['count']
                for rank in (0, count//2, count-1):
                    actual = query(budget, rank, filtered=filtered)
                    x, y = map(int, actual['point'])
                    self.assertEqual(x+2*y, budget)
                    if filtered:
                        self.assertEqual((x % 3, y % 5), (1, 2))
        for args in ((True, 0), (-1, 0), (2**64, 0), (10, True), (10, 6), (0, 0, (3, 5), True)):
            with self.assertRaises(ValueError):
                query(*args)

    def test_transport_rejects_source_and_encoder_changes(self):
        packet = machine()['transport']
        for key in ('source', 'encoder', 'readout'):
            altered = json.loads(encoded(packet))
            if key == 'source':
                altered['original']['operators'][0]['matrix'][0][3] = 1
            elif key == 'encoder':
                altered['encoder'][0][3] = 1
            else:
                altered['original']['readouts'][0][3] = 1
            self.assertFalse(verify_cost_quotient(altered))

    def test_connected_results(self):
        result = build_results()
        self.assertEqual(result['population']['count'], '500000000001')
        self.assertEqual(result['restricted_population']['count'], '33333333333')
        self.assertEqual(result['machine']['minimal_realization']['dimension'], 3)
        self.assertNotEqual(Q(result['machine']['minimal_realization']['hankel_determinant']), 0)
        lo, hi = map(Q, result['analytic']['interval'])
        self.assertLessEqual(lo, Q(512, 441)); self.assertGreaterEqual(hi, Q(512, 441))
        self.assertFalse(result['binary']['stored_point_one']['is_power'])
        self.assertTrue(result['binary']['stored_quarter']['is_power'])
        self.assertEqual(result['binary']['round_once_cancellation'], '1')
        self.assertFalse(result['telescoping']['power_window']['unbounded_classification_proved'])


if __name__ == '__main__':
    unittest.main()
