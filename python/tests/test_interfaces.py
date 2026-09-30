"""The finite claims behind PerfectPower/Interfaces.lean match the committed data."""
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class A048624Terms(unittest.TestCase):
    def test_lean_terms_are_the_seq_prefix(self):
        lean = (ROOT / 'PerfectPower' / 'Interfaces.lean').read_text()
        block = re.search(r'def A048624_terms : List ℤ :=\s*\[([^\]]*)\]', lean).group(1)
        lean_terms = [int(t) for t in block.split(',')]
        seq = next((ROOT / 'data' / 'oeis').rglob('A048624.seq')).read_text()
        terms = []
        for line in seq.splitlines():
            if line[:2] in ('%S', '%T', '%U'):
                terms += [int(t) for t in line.split(' ', 2)[2].split(',') if t.strip()]
        self.assertEqual(lean_terms, terms[:len(lean_terms)])
        self.assertEqual(len(lean_terms), 16)

    def test_shift_two_is_the_only_small_shift(self):
        # Mirror of A048624_terms_match; uniqueness over all shifts is the Lean theorem.
        def B(n):
            a, b = 1, 0
            for _ in range(n):
                a, b = a + 2 * b, a + b
            return b
        lean_terms = [B(n + 2) for n in range(16)]
        self.assertEqual([s for s in range(40) if [B(n + s) for n in range(16)] == lean_terms], [2])


if __name__ == '__main__':
    unittest.main()
