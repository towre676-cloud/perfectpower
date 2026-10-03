import random
import unittest
from perfectpower.smt_cert import split_commands
from perfectpower.smt_stream import split_commands_fast


class SMTStreamTests(unittest.TestCase):
    def test_strings_comments_and_quoted_names(self):
        source = '; leading )\n(set-info :source |( ; " anything\n) |)\n(set-info :notes "a ""quoted"" (;|) string")\n(declare-const |x;()| Int) ; )\n(assert (= |x;()| 1))'
        self.assertEqual(split_commands_fast(source), split_commands(source))

    def test_random_exact_slices(self):
        rng = random.Random(107)
        atoms = ['x', '|x;()|', '"a ""b"" (;)"', '12', '(- 7)']
        for _ in range(1000):
            commands = ['(assert (= ' + rng.choice(atoms) + ' ' + rng.choice(atoms) + '))' for _ in range(rng.randrange(1, 15))]
            separators = ['\n; )( \"|\n', ' ', '\n', '\t']
            source = ''.join(c + rng.choice(separators) for c in commands)
            self.assertEqual(split_commands_fast(source), commands)
            self.assertEqual(split_commands_fast(source), split_commands(source))

    def test_malformed_input(self):
        for source in ('(', ')', '(assert "unterminated)', '(assert |unterminated)', '"unterminated'):
            with self.assertRaises(ValueError):
                split_commands_fast(source)

    def test_empty(self):
        self.assertEqual(split_commands_fast('; comment\n'), [])


if __name__ == '__main__':
    unittest.main()
