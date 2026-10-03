import unittest
from unittest.mock import patch
import z3
from perfectpower.industrial_router import route_lia
from perfectpower.industrial_portfolio import solve_stream
from perfectpower.smt_cert import split_commands, head


class IndustrialPerformanceTests(unittest.TestCase):
    def test_assertions_preserved(self):
        s = '(set-logic QF_NIA)(declare-const x Int)(declare-const b Bool)(assert (or b (= (div (* 3 x) 7) 4)))(check-sat)'
        r, ok = route_lia(s)
        self.assertTrue(ok)
        self.assertEqual([c for c in split_commands(s) if head(c)=='assert'], [c for c in split_commands(r) if head(c)=='assert'])

    def test_fail_closed(self):
        for atom in ('(= (* x x) 4)', '(= (div x x) 2)', '(= (div x 0) 2)', '(= x b)', '(= y 2)', '(forall ((y Int)) (= y x))'):
            s = f'(set-logic QF_NIA)(declare-const x Int)(declare-const b Bool)(assert {atom})(check-sat)'
            self.assertEqual(route_lia(s), (s, False))

    def test_scopes(self):
        s = '(set-logic QF_NIA)(push 1)(declare-const x Int)(assert (= x 1))(pop 1)(assert (= x 1))'
        self.assertFalse(route_lia(s)[1])
        self.assertFalse(route_lia('(set-logic QF_NIA)(pop 1)')[1])

    def test_incremental(self):
        s = '(set-logic QF_NIA)(declare-const x Int)(assert (= x 1))(check-sat)(push 1)(assert (= x 2))(check-sat)(pop 1)(check-sat)'
        for portfolio in (False, True):
            r = solve_stream(s, portfolio=portfolio)
            self.assertEqual(r['errors'], [])
            self.assertEqual([q['answer'] for q in r['queries']], ['sat', 'unsat', 'sat'])

    def test_nonlinear_original(self):
        r = solve_stream('(set-logic QF_NIA)(declare-const x Int)(assert (= (* x x) 2))(check-sat)', portfolio=True)
        self.assertFalse(r['eligible'])
        self.assertEqual(r['queries'][0]['answer'], 'unsat')

    def test_budget_validation(self):
        with self.assertRaises(ValueError):
            solve_stream('(check-sat)', 1, True)

    def test_signed_division_semantics(self):
        for n in range(-8, 9):
            for d in (-7, -2, 2, 7):
                def lit(v):
                    return str(v) if v >= 0 else f'(- {-v})'
                s = f'(set-logic QF_NIA)(declare-const x Int)(assert (= x {lit(n)}))(assert (= (div x {lit(d)}) {lit(n // d if d > 0 else -(n // -d))}))(check-sat)'
                original = solve_stream(s)
                candidate = solve_stream(s, portfolio=True)
                self.assertTrue(candidate['eligible'])
                self.assertEqual(original['errors'], [])
                self.assertEqual(candidate['errors'], [])
                self.assertEqual(candidate['queries'][0]['answer'], 'sat')
                self.assertEqual(original['queries'][0]['answer'], candidate['queries'][0]['answer'])

    def test_fallback_budget_and_timeout_reset(self):
        actual = z3.z3core.Z3_eval_smtlib2_string
        calls = []
        checks = 0
        def wrapped(context, command):
            nonlocal checks
            calls.append(command)
            if command == '(check-sat)':
                checks += 1
                if checks == 1:
                    return 'unknown'
            return actual(context, command)
        with patch.object(z3.z3core, 'Z3_eval_smtlib2_string', side_effect=wrapped):
            r = solve_stream('(set-logic QF_NIA)(declare-const x Int)(assert (= x 1))(check-sat)', 251, True)
        self.assertEqual(r['errors'], [])
        self.assertEqual(r['fallback_queries'], 1)
        self.assertEqual(r['queries'][0]['answer'], 'sat')
        timeouts = [c for c in calls if c.startswith('(set-option :timeout')]
        self.assertEqual(timeouts, ['(set-option :timeout 125)', '(set-option :timeout 0)', '(set-option :timeout 126)', '(set-option :timeout 0)'])


if __name__ == '__main__':
    unittest.main()
