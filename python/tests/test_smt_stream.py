import random
import unittest
from perfectpower.smt_cert import split_commands
from perfectpower.smt_stream import split_commands_fast, iter_commands, file_chunks
from io import StringIO


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

    def test_every_chunk_boundary(self):
        source = '; hi )\n(set-info :notes "a ""quoted"" (;|) string")\n(declare-const |x;()| Int) ; )\n(assert (= |x;()| 1))'
        expected = split_commands(source)
        for boundary in range(len(source)+1):
            self.assertEqual(list(iter_commands([source[:boundary], '', source[boundary:]])), expected)
        self.assertEqual(list(iter_commands(source)), expected)
        for width in range(1, 19):
            self.assertEqual(list(iter_commands(file_chunks(StringIO(source), width))), expected)

    def test_stream_limits_and_bad_tail(self):
        self.assertEqual(list(iter_commands(['(a)'], max_command_chars=3)), ['(a)'])
        for chunks, kwargs in [(['(a)'], {'max_command_chars':2}),
                               (['(a)'], {'max_chunk_chars':2}),
                               (['(a)'], {'max_command_chars':0}),
                               ([b'(a)'], {}), (['garbage'], {}),
                               (['(a "x'], {}), (['(a |x'], {}), ([')'], {})]:
            with self.assertRaises(ValueError):
                list(iter_commands(chunks, **kwargs))
        stream = iter_commands(['(a)', '(bad'])
        self.assertEqual(next(stream), '(a)')
        with self.assertRaises(ValueError):
            next(stream)

    def test_source_is_consumed_on_demand(self):
        def chunks():
            yield '(a)'
            self.fail('read beyond the first complete command')
        stream = iter_commands(chunks())
        self.assertEqual(next(stream), '(a)')
        stream.close()


if __name__ == '__main__':
    unittest.main()
