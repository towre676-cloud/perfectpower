"""The Galois front end (perfectpower.galois): orbits of the roots and the reason for the type."""
import random
import unittest

from perfectpower.atlas import classify
from perfectpower.compiler import pmul, ppow
from perfectpower.galois import galois_profile


class Galois(unittest.TestCase):
    def test_pell_is_a_conjugate_pair(self):
        g = galois_profile((1, 0, 2), 2)                        # 2n^2 + 1
        (o,) = g['orbits']
        self.assertEqual((o['size'], o['group'], o['field'], o['t']), (2, 'C2', 'Q(sqrt(-2))', 2))
        self.assertTrue(g['explanation'].startswith('Pell type'))

    def test_radical_root_is_fixed(self):
        g = galois_profile((0, 1), 3)
        self.assertEqual(g['orbits'][0]['group'], 'trivial')
        self.assertTrue(g['explanation'].startswith('radical type'))

    def test_cubic_groups(self):
        s3 = galois_profile((-2, 0, 0, 1), 2)['orbits'][0]    # x^3 - 2
        a3 = galois_profile((1, -3, 0, 1), 2)['orbits'][0]    # x^3 - 3x + 1, discriminant 81
        self.assertEqual((s3['group'], a3['group'], a3['discriminant']), ('S3', 'A3', '81'))

    def test_split_pell(self):
        g = galois_profile(pmul((-1, 1), (-2, 1)), 2)          # (n - 1)(n - 2)
        self.assertEqual([o['group'] for o in g['orbits']], ['trivial', 'trivial'])
        self.assertIn('both rational', g['explanation'])

    def test_explanation_agrees_with_classifier(self):
        rng = random.Random(3)
        for _ in range(300):
            parts = [tuple(rng.randint(-4, 4) for _ in range(rng.choice([1, 2, 3]))) +
                     (rng.choice([1, 2, -1]),) for _ in range(rng.choice([1, 2]))]
            F = (1,)
            for q in parts:
                F = pmul(F, ppow(q, rng.choice([1, 1, 2, 3])))
            if len(F) < 2:
                continue
            d = rng.choice([2, 3, 4, 6])
            word = galois_profile(F, d)['explanation'].split()[0].lower()
            self.assertEqual(word, classify(F, d).kind, (F, d))


if __name__ == '__main__':
    unittest.main()
