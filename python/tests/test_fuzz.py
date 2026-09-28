"""Small fixed-seed runs of the differential fuzzers (python/fuzz/); `make fuzz` runs them in full."""
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'fuzz'))
import fuzz_finite_bucket_late_hits  # noqa: E402
import fuzz_pell_quadratic  # noqa: E402
import fuzz_structural_vs_scan  # noqa: E402
from perfectpower.core import hit_indices  # noqa: E402
from perfectpower.sieve import sieve_hits  # noqa: E402


class Fuzz(unittest.TestCase):
    def test_structural_vs_scan(self):
        for seed in (1, 2, 3):
            r = fuzz_structural_vs_scan.run(seed, 150, N=2000)
            self.assertEqual(r['disagreements'], [])
            self.assertEqual(r['errors'], [])

    def test_pell_quadratic(self):
        r = fuzz_pell_quadratic.run(7, 25, N=50000)
        self.assertEqual(r['bad'], [])

    def test_sieve_matches_scan(self):
        import random
        rng = random.Random(5)
        for _ in range(60):
            deg, d = rng.choice([1, 2, 3, 4, 5]), rng.choice([2, 3, 4, 5])
            f = [rng.randint(-9, 9) for _ in range(deg)] + [rng.choice([1, 2, 3, -1, 4, 9])]
            self.assertEqual(sieve_hits(f, d, 2001), [n for n, _ in hit_indices(f, d, 0, 2000)])

    def test_known_late_hit(self):
        # n^3 + 2n^2 - 3n - 1 = m^2 at n = 47882 (the external fuzzer's find), exactly
        self.assertEqual(sieve_hits([-1, -3, 2, 1], 2, 10 ** 6), [2, 47882])

    def test_finite_bucket_runs(self):
        r = fuzz_finite_bucket_late_hits.run(11, 60, scan=20000)
        self.assertGreater(r['finite_tested'], 0)


if __name__ == '__main__':
    unittest.main()
