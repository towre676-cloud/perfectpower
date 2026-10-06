import random
import unittest
from unittest.mock import patch
import z3
from perfectpower.industrial_replay import solve_replay, solve_replay_stream
from perfectpower.industrial_portfolio import solve_stream


class IndustrialReplayTests(unittest.TestCase):
    def test_incremental_and_assumptions(self):
        s = '(set-logic QF_NIA)(declare-const x Int)(declare-const b Bool)(assert (= x 1))(check-sat)(push 1)(assert (= x 2))(check-sat)(pop 1)(assert b)(check-sat-assuming ((not b)))(check-sat)'
        for fast in (False, True):
            for bound in (0, 1, 64, 262144):
                r = solve_replay(s, batch_chars=bound, fast_split=fast)
                self.assertEqual(r['errors'], [])
                self.assertEqual([q['answer'] for q in r['queries']], ['sat', 'unsat', 'unsat', 'sat'])

    def test_randomized_query_traces(self):
        rng = random.Random(107)
        for _ in range(40):
            commands = ['(set-logic QF_NIA)', '(declare-const x Int)']
            expected = []
            for _ in range(8):
                a, b = rng.randrange(9), rng.randrange(9)
                commands.extend(['(push 1)', f'(assert (= x {a}))', f'(assert (<= x {b}))', '(check-sat)', '(pop 1)'])
                expected.append('sat' if a <= b else 'unsat')
            s = '\n'.join(commands)
            for fast in (False, True):
                for bound in (0, 79, 262144):
                    r = solve_replay(s, batch_chars=bound, fast_split=fast)
                    self.assertEqual(r['errors'], [])
                    self.assertEqual([q['answer'] for q in r['queries']], expected)

    def test_error_stops_before_next_query(self):
        s = '(set-logic QF_NIA)(declare-const x Int)(assert (= missing 1))(check-sat)(check-sat)'
        for bound in (0, 262144):
            r = solve_replay(s, batch_chars=bound)
            self.assertTrue(r['errors'])
            self.assertEqual(r['queries'], [])

    def test_timeout_barriers(self):
        actual = z3.z3core.Z3_eval_smtlib2_string
        calls = []
        def wrapped(context, command):
            calls.append(command)
            return actual(context, command)
        s = '(set-logic QF_NIA)(declare-const x Int)(assert (= x 1))(check-sat)(push 1)(assert (= x 2))(check-sat)(pop 1)'
        with patch.object(z3.z3core, 'Z3_eval_smtlib2_string', side_effect=wrapped):
            r = solve_replay(s)
        self.assertEqual(r['errors'], [])
        for i, c in enumerate(calls):
            if c == '(check-sat)':
                self.assertEqual(calls[i-1], '(set-option :timeout 250)')
                self.assertEqual(calls[i+1], '(set-option :timeout 0)')
        self.assertIn('(pop 1)', calls[-1])

    def test_transport_calls_and_bounds(self):
        s = '(set-logic QF_NIA)(declare-const x Int)' + '(assert (>= x 0))'*100 + '(check-sat)'
        original = solve_replay(s, batch_chars=0)
        batched = solve_replay(s, batch_chars=64)
        self.assertEqual(original['ingestion_calls'], 102)
        self.assertLess(batched['ingestion_calls'], 40)
        self.assertLessEqual(batched['peak_batch_chars'], 64)
        oversized = solve_replay('(declare-const variable_with_a_long_name Int)(check-sat)', batch_chars=1)
        self.assertEqual(oversized['errors'], [])
        self.assertGreater(oversized['peak_batch_chars'], 1)

    def test_control_matches_previous_engine(self):
        s = '(set-logic QF_NIA)(declare-const x Int)(assert (= (* x x) 2))(check-sat)'
        self.assertEqual(solve_replay(s, batch_chars=0)['queries'][0]['answer'], solve_stream(s)['queries'][0]['answer'])

    def test_validation(self):
        with self.assertRaises(ValueError):
            solve_replay('(check-sat)', batch_chars=-1)

    def test_stream_matches_control_at_all_boundaries(self):
        s = '(declare-const |x;()| Int)(assert (= |x;()| 1))(check-sat)(push 1)(assert (= |x;()| 2))(check-sat)(pop 1)(check-sat)'
        for width in (1, 2, 7, 64):
            for bound in (0, 1, 79, 262144):
                chunks = (s[i:i+width] for i in range(0, len(s), width))
                result = solve_replay_stream(chunks, batch_chars=bound)
                self.assertEqual(result['errors'], [])
                self.assertEqual([q['answer'] for q in result['queries']], ['sat', 'unsat', 'sat'])
                self.assertEqual(result['source_commands'], 8)

    def test_stream_sink_is_online_and_bad_tail_stops(self):
        rows = []
        def source():
            yield '(check-sat)'
            self.assertEqual([r['answer'] for r in rows], ['sat'])
            yield '(bad'
        result = solve_replay_stream(source(), query_sink=rows.append)
        self.assertEqual(result['queries'], [])
        self.assertEqual(result['query_count'], 1)
        self.assertTrue(result['errors'])
        self.assertEqual(result['source_commands'], 1)

    def test_stream_oversized_input_never_reaches_solver(self):
        result = solve_replay_stream(['(declare-const long_name Int)(check-sat)'], max_command_chars=12)
        self.assertTrue(result['errors'])
        self.assertEqual(result['native_calls'], 0)


if __name__ == '__main__':
    unittest.main()
