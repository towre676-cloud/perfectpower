"""The evidence gates must reject corrupted data (census domain and rows, binomial receipt)."""
import copy
import json
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'crosscheck'))
import check_binomial  # noqa: E402
import mordell_census  # noqa: E402


class CensusGate(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = [json.loads(line) for line in open(ROOT / 'data' / 'mordell_census.jsonl')]

    def test_committed_census_passes(self):
        mordell_census.check_domain(self.rows, 10000)
        for r in self.rows:
            mordell_census.check_row(r)

    def rejects(self, rows):
        with self.assertRaises(AssertionError):
            mordell_census.check_domain(rows, 10000)
            for r in rows:
                mordell_census.check_row(r)

    def test_duplicate_and_omission_keep_count(self):
        rows = self.rows[:5] + [self.rows[4]] + self.rows[6:]
        self.assertEqual(len(rows), len(self.rows))
        self.rejects(rows)

    def test_out_of_bound(self):
        self.rejects(self.rows[1:] + [dict(self.rows[0], k=10001)])

    def test_unsorted_or_duplicated_x(self):
        i = next(i for i, r in enumerate(self.rows) if len(r['x_coordinates']) > 1)
        r = self.rows[i]
        for xs in (r['x_coordinates'][::-1], r['x_coordinates'] + r['x_coordinates'][-1:]):
            self.rejects(self.rows[:i] + [dict(r, x_coordinates=xs)] + self.rows[i + 1:])

    def test_failed_scan_cannot_be_independent(self):
        i = next(i for i, r in enumerate(self.rows) if r['certification'] == 'INDEPENDENT_COMPUTATION')
        r = dict(self.rows[i], scan_x_abs_le_1e5=self.rows[i]['scan_x_abs_le_1e5'] + [99999])
        self.rejects(self.rows[:i] + [r] + self.rows[i + 1:])
        r['scan_agrees'] = False            # consistent flag, but the label must then change
        self.rejects(self.rows[:i] + [r] + self.rows[i + 1:])

    def test_off_curve_point(self):
        i = next(i for i, r in enumerate(self.rows) if r['x_coordinates'])
        r = copy.deepcopy(self.rows[i])
        r['x_coordinates'][0] += 1
        r['x_hash'] = mordell_census.xs_hash(r['x_coordinates'])
        self.rejects(self.rows[:i] + [r] + self.rows[i + 1:])


class BinomialGate(unittest.TestCase):
    def test_lean_hypotheses_parse(self):
        src = (ROOT / 'PerfectPower' / 'Binomial.lean').read_text()
        self.assertEqual(check_binomial.lean_hypothesis_xs(src, 'IntegralPointsCubePlusOne'), [-1, 0, 2])
        self.assertEqual(check_binomial.lean_hypothesis_xs(src, 'IntegralPointsCongruent6'),
                         [-6, -3, -2, 0, 6, 12, 18, 294])
        self.assertEqual(check_binomial.lean_hit_lists(src), [[1, 2], [1, 2, 3, 4, 50]])


if __name__ == '__main__':
    unittest.main()
