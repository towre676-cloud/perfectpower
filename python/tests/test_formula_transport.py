import unittest
from perfectpower.formula_transport import emit_square_cube

BASE = '''(set-logic QF_NIA)
(declare-const a Int)(declare-const b Int)
(assert (= (* a a) (* b b b)))
(assert (and (>= a (- 10)) (or (= b 0) (= b 4))))
(check-sat)'''

class FormulaTransportTests(unittest.TestCase):
    def test_emit_retains_context(self):
        s = emit_square_cube(BASE)
        self.assertIn('FormulaTransport.square_cube_exists residual', s)
        self.assertIn('x ≥ (-(10 : ℤ))', s)
        self.assertIn('y = (4 : ℤ)', s)
        self.assertIn('Source SHA256:', s)

    def test_swapped_relation(self):
        s = emit_square_cube(BASE.replace('(* a a) (* b b b)', '(* b b b) (* a a)'))
        self.assertIn("square coordinate 'a'; cube coordinate 'b'", s)

    def test_rejections(self):
        cases = [BASE.replace('a Int', 'a Real'),
                 BASE.replace('(* a a)', '(* a b)'),
                 BASE.replace('(>= a (- 10))', '(= (div a 2) b)'),
                 BASE.replace('(>= a (- 10))', '(= (mod a 2) b)'),
                 BASE.replace('(check-sat)', '(push 1)(check-sat)'),
                 BASE + '(check-sat)',
                 BASE + '(assert false)',
                 BASE.replace('a Int', '|bad name| Int'),
                 BASE.replace('(declare-const b Int)', '(declare-const b Int)(declare-const c Int)'),
                 BASE.replace('(assert (= (* a a) (* b b b)))', '(assert (not (= (* a a) (* b b b))))')]
        for c in cases:
            with self.subTest(c=c), self.assertRaises(ValueError):
                emit_square_cube(c)

if __name__ == '__main__':
    unittest.main()
