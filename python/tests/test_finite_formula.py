import hashlib
import random
import unittest
from perfectpower.finite_formula import emit_finite_query, _positive_source


def script(r,s,a,b,k,extra=''):
    cube=f'(+ (* {r} n) {s})'
    square=f'(+ (* {a} m) {b})'
    def negnum(t):
        import re
        return re.sub(r'(?<![A-Za-z0-9_])-([0-9]+)',r'(- \1)',t)
    return negnum(f'''(declare-const n Int)(declare-const m Int)
(assert (= (* {square} {square}) (+ (* {cube} {cube} {cube}) {k})))
{extra}(check-sat)''')

class FiniteFormulaTests(unittest.TestCase):
    def test_random_affine_lattices(self):
        rng=random.Random(676)
        for _ in range(300):
            r=rng.choice([-5,-3,-2,-1,1,2,3,5]);s=rng.randrange(-8,9)
            a=rng.choice([-4,-2,-1,1,2,4]);b=rng.randrange(-5,6);k=rng.choice([-1,2])
            text=script(r,s,a,b,k)
            out=emit_finite_query(text)
            expected={(n,m) for n in range(-12,13) for m in range(-12,13)
                      if (a*m+b)**2==(r*n+s)**3+k}
            observed={p for p in out.points if all(-12<=v<=12 for v in p)}
            self.assertEqual(expected,observed,(r,s,a,b,k))
            for n,m in out.points:
                self.assertEqual((a*m+b)**2,(r*n+s)**3+k)
            self.assertEqual(out.source_sha256,hashlib.sha256(text.encode()).hexdigest())

    def test_existing_registry(self):
        self.assertGreaterEqual(sum(_positive_source(k) is not None for k in range(1,101)),73)
        out=emit_finite_query(script(1,0,1,0,17))
        self.assertIn((5234,378661),out.points)
        self.assertIn((5234,-378661),out.points)
        self.assertEqual(len(out.points),16)
        self.assertEqual(emit_finite_query(script(1,0,1,0,11)).points,[])
        self.assertEqual(emit_finite_query(script(1,0,1,0,22)).points,[(3,-7),(3,7)])
        self.assertIsNone(_positive_source(19))

    def test_extra_variable(self):
        text=script(3,2,2,1,2).replace('(check-sat)',
            '(declare-const z Int)(assert (= z (+ n m)))(check-sat)')
        out=emit_finite_query(text)
        self.assertIn('(z0 : ℤ)',out.lean)
        self.assertIn('z0 = (x + y)',out.lean)
        self.assertEqual(out.points,[(-1,-1),(-1,0)])

    def test_quartic(self):
        out=emit_finite_query('(declare-const u Int)(declare-const v Int)'
            '(assert (= (* v v) (+ (* 3 u u u u) (* 3 u u) 1)))'
            '(assert (> u 0))(check-sat)')
        self.assertEqual(out.points,[(0,-1),(0,1)])
        self.assertIn('QuarticPilot.complete',out.lean)

    def test_smt_residual_equivalence(self):
        import z3
        text=script(-2,1,2,1,2,
            '(declare-const z Int)(assert (and (= z (+ n m)) (not (= z 2))))')
        out=emit_finite_query(text)
        original=z3.And(list(z3.parse_smt2_string(text)))
        reduced=z3.And(list(z3.parse_smt2_string(out.smt)))
        n,m,z=z3.Ints('n m z')
        for nv in range(-4,5):
            for mv in range(-4,5):
                for zv in range(-2,3):
                    bindings=((n,z3.IntVal(nv)),(m,z3.IntVal(mv)),(z,z3.IntVal(zv)))
                    lhs=z3.simplify(z3.substitute(original,*bindings))
                    rhs=z3.simplify(z3.substitute(reduced,*bindings))
                    self.assertEqual(z3.is_true(lhs),z3.is_true(rhs),(nv,mv,zv))

    def test_unsupported(self):
        base=script(1,0,1,0,2)
        for text in [script(1,0,1,0,19),script(1,0,1,0,0),
                     base.replace('m Int','m Real'),base+'(check-sat)',
                     base.replace('(check-sat)','(push 1)(check-sat)'),
                     base.replace('(check-sat)','(assert (= (div n 2) m))(check-sat)'),
                     base.replace('(check-sat)','(assert (= (mod n 2) m))(check-sat)'),
                     base.replace('(check-sat)','(assert (forall ((z Int)) (= z n)))(check-sat)')]:
            with self.subTest(text=text),self.assertRaises(ValueError):emit_finite_query(text)

if __name__=='__main__':unittest.main()
