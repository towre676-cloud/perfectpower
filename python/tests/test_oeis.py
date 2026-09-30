"""The OEIS layer (perfectpower.oeis) on a synthetic snapshot: no OEIS data is used here.

The fake entries are built from PerfectPower's own coordinates, so each of the four outcomes is
exercised with a known answer."""
import unittest

from perfectpower.oeis import (atlas, premise_candidates, problems, square_triangular_cluster,
                               _check_recurrence)


class Cluster(unittest.TestCase):
    def test_six_coordinates_of_one_orbit(self):
        c = {co['key']: co for co in square_triangular_cluster(20)['coordinates']}
        self.assertEqual(c['PellIdx']['terms'][:4], [2, 12, 70, 408])
        self.assertEqual(c['SqTriRoot']['terms'][:4], [1, 6, 35, 204])
        self.assertEqual(c['TriIdx']['terms'][:4], [1, 8, 49, 288])
        self.assertEqual(c['SqTri']['terms'][:4], [1, 36, 1225, 41616])
        # the coordinate maps, exactly
        for n, t, u, v, m in zip(c['PellIdx']['terms'], c['SqTriRoot']['terms'], c['TriIdx']['terms'],
                                 c['SqTri']['terms'], c['PellRoot']['terms']):
            self.assertEqual((n, v, 2 * t * t, m * m), (2 * t, t * t, u * (u + 1), 2 * n * n + 1))
        # same orbit, different constants: the values grow twice as fast
        self.assertAlmostEqual(c['SqTri']['count_constant_value'] * 2, c['SqTriRoot']['count_constant_value'])
        self.assertAlmostEqual(c['OddSqTri']['count_constant_value'] * 4, c['SqTriRoot']['count_constant_value'])

    def test_recurrences(self):
        for co in square_triangular_cluster(25)['coordinates']:
            if co['recurrence']:
                self.assertTrue(_check_recurrence(co['terms'], co['recurrence']), co['key'])

    def test_counts_against_brute_force(self):
        # the constant log N / (r log eps) is visible already at N = 10^40
        import math
        c = {co['key']: co for co in square_triangular_cluster(60)['coordinates']}
        N = 10 ** 40
        for key in ('SqTriRoot', 'SqTri', 'OddSqTri'):
            cnt = sum(1 for x in c[key]['terms'] if x <= N)
            self.assertLess(abs(cnt - c[key]['count_constant_value'] * math.log(N)), 2, key)

    def test_plan_problems_are_exported(self):
        names = {p['problem'] for p in problems()}
        self.assertIn('plan_late_certified', names)
        late = next(p for p in problems() if p['problem'] == 'plan_late_certified')
        self.assertEqual(late['least'], 655680)


class Atlas(unittest.TestCase):
    def setUp(self):
        c = {co['key']: co['terms'] for co in square_triangular_cluster(30)['coordinates']}
        bad = list(c['SqTriRoot'][:12])
        bad[8] += 1
        self.snap = {
            'A900001': [0] + c['SqTri'][:20],             # same terms, offset 1
            'A900002': [x * 3 for x in c['SqTriRoot'][:20]],  # unrelated scaling: no match
            'A900003': [0, 0] + bad,                      # agrees on 8 terms, then differs
            'A900004': [x * x for x in c['PellRoot'][:15]],  # PellRoot squared: a transformation
        }

    def outcomes(self, reviewed=None):
        return {(r['coordinate'], r['oeis']): r for r in atlas(self.snap, reviewed,
                                                               probs=[square_triangular_cluster(30)])}

    def test_four_outcomes(self):
        out = self.outcomes()
        r = out[('SqTri', 'A900001')]
        self.assertEqual(r['outcome'], 'TERMS_AGREE_UNPROVED')
        self.assertIn('PerfectPower.SquareTriangular.sqTri_iff', r['lean_candidate'])
        self.assertEqual(out[('SqTriRoot', 'A900003')]['outcome'], 'REJECTED')
        self.assertEqual(out[('SqTriRoot', 'A900003')]['first_counterexample']['our_index'], 8)
        self.assertEqual(out[('PellRoot', 'A900004')]['outcome'], 'RELATED_BY_TRANSFORMATION')
        self.assertEqual(out[('PellRoot', 'A900004')]['transformation'], 'x^2')
        self.assertFalse(any(k[1] == 'A900002' and k[0] == 'SqTriRoot' for k in out))
        # a review of the definition is what upgrades agreement to a proved equivalence
        out = self.outcomes({'A900001': 'definition read: square triangular numbers'})
        self.assertEqual(out[('SqTri', 'A900001')]['outcome'], 'DEFINITION_PROVED_EQUIVALENT')

    def test_no_snapshot_content_in_records(self):
        for r in atlas(self.snap, probs=[square_triangular_cluster(30)]):
            self.assertNotIn('terms', r)
            self.assertNotIn('name', r)


class Leads(unittest.TestCase):
    def test_premise_candidates_rank_completeness(self):
        names = {'A900010': 'Numbers n such that n^3 + 17 is a square.',
                 'A900011': 'All integral points: values x with x^3 + 17 a square (complete list).',
                 'A900012': 'Numbers n such that n^3 + 170 is a square.'}
        curves = [{'k': 17, 'x_found_by_scan': [-2, -1, 2, 4, 8, 43, 52, 5234]}]
        out = premise_candidates(names, curves)
        self.assertEqual([r['oeis'] for r in out], ['A900011', 'A900010'])


if __name__ == '__main__':
    unittest.main()
