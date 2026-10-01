"""Soundness at the replacement boundary (`perfectpower.smt_cert`).  Skipped without z3-solver."""
import copy
import sys
import unittest
from math import isqrt
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

try:
    import z3
except ImportError:
    z3 = None

SCRIPT = """(set-logic QF_NIA)
(declare-fun n () Int)
(declare-fun m () Int)
(declare-fun p () Bool)
(assert (>= (+ n m) (- 1000)))
(push 1)
(assert (and p (= (* m m) (- (* (+ (* 3 n) 15) (+ (* 3 n) 15) (+ (* 3 n) 15)) 56))))
(check-sat)
(pop 1)
(check-sat)
"""


@unittest.skipIf(z3 is None, 'z3-solver not installed')
class Boundary(unittest.TestCase):
    def setUp(self):
        from perfectpower import smt_cert
        self.sc = smt_cert

    def ledger(self, text):
        import hashlib
        cmds = self.sc.split_commands(text)
        queries, ctx = self.sc.replay(cmds)
        sha = hashlib.sha256(text.encode()).hexdigest()
        recs = {i: self.sc.classify_assert(cmds, i, ctx[i], sha) for i, c in enumerate(cmds)
                if self.sc.head(c) == 'assert'}
        return cmds, queries, recs

    def cert_of(self, text):
        _, _, recs = self.ledger(text)
        certs = [r.certificate for rs in recs.values() for r in rs if r.certificate]
        return certs[0] if certs else None

    # -- incremental assumptions: the certificate lives only where its assertion is live
    def test_live_stack(self):
        cmds, queries, recs = self.ledger(SCRIPT)
        self.assertEqual(len(queries), 2)
        live = [[r for a in q.live_asserts for r in recs[a] if r.certificate] for q in queries]
        self.assertEqual(len(live[0]), 1)
        self.assertEqual(live[1], [])
        cert = live[0][0].certificate
        self.assertEqual(cert['witnesses'], [[1, -76], [1, 76]])
        ok, why = self.sc.check_certificate(cert, SCRIPT)
        self.assertTrue(ok, why)

    # -- binding
    def test_wrong_binding(self):
        cert = self.cert_of(SCRIPT)
        self.assertFalse(self.sc.check_certificate(cert, SCRIPT.replace('1000', '999'))[0])
        c2 = dict(cert, command_index=cert['command_index'] - 1)
        self.assertFalse(self.sc.check_certificate(c2, SCRIPT)[0])
        c3 = dict(cert, atom=cert['atom'].replace('56', '57'))
        self.assertFalse(self.sc.check_certificate(c3, SCRIPT)[0])

    # -- tampering
    def test_changed_coefficients_and_malformed(self):
        cert = self.cert_of(SCRIPT)
        bad = copy.deepcopy(cert)
        bad['polynomial'][0][1] += 1
        self.assertFalse(self.sc.check_certificate(bad, SCRIPT)[0])
        bad = copy.deepcopy(cert)
        bad['affine']['k'] = -57
        self.assertFalse(self.sc.check_certificate(bad, SCRIPT)[0])
        bad = copy.deepcopy(cert)
        del bad['theorem']
        self.assertFalse(self.sc.check_certificate(bad, SCRIPT)[0])
        self.assertFalse(self.sc.check_certificate({'version': 2}, SCRIPT)[0])

    def test_relation_is_certified(self):
        # the reviewer's attack: the same operands under '>' with every binding field consistent
        import hashlib
        cert = self.cert_of(SCRIPT)
        ineq = SCRIPT.replace('(= (* m m) (- (* (+ (* 3 n) 15)', '(> (* m m) (- (* (+ (* 3 n) 15)')
        self.assertNotEqual(ineq, SCRIPT)
        cmds = self.sc.split_commands(ineq)
        _, ctx = self.sc.replay(cmds)
        idx = cert['command_index']
        parsed = z3.parse_smt2_string('\n'.join(cmds[d] for d in ctx[idx]) + '\n' + cmds[idx])
        atom = [c for a in parsed for c in self.sc._conjuncts(a) if z3.is_gt(c)][0]
        forged = dict(cert, source_sha256=hashlib.sha256(ineq.encode()).hexdigest(),
                      assert_sha256=hashlib.sha256(cmds[idx].encode()).hexdigest(), atom=atom.sexpr())
        ok, why = self.sc.check_certificate(forged, ineq)
        self.assertFalse(ok)
        self.assertIn('equality', why)
        # the inequality really differs from the replacement: (n, m) = (-5, 0) satisfies it
        # ((3n + 15)^3 - 56 = -56 < 0), while the certified list only allows n = 1
        point = [(z3.Int('n'), z3.IntVal(-5)), (z3.Int('m'), z3.IntVal(0))]
        self.assertTrue(z3.is_true(z3.simplify(z3.substitute(atom, *point))))
        self.assertTrue(z3.is_false(z3.simplify(z3.substitute(self.sc.replacement_formula(cert), *point))))
        # a certificate that omits or changes the relation field is rejected too
        self.assertFalse(self.sc.check_certificate(dict(cert, relation='>'), SCRIPT)[0])
        self.assertFalse(self.sc.check_certificate({k: v for k, v in cert.items() if k != 'relation'}, SCRIPT)[0])
        self.assertTrue(self.sc.check_certificate(cert, SCRIPT)[0])

    def test_even_power_sign_loss_rejected(self):
        cert = self.cert_of(SCRIPT)
        bad = copy.deepcopy(cert)
        bad['witnesses'] = [[1, 76]]
        self.assertFalse(self.sc.check_certificate(bad, SCRIPT)[0])

    # -- domains: no n >= 1 contract; negative and zero inputs are covered
    def test_negative_and_zero_inputs(self):
        s = """(declare-fun n () Int)(declare-fun m () Int)
(assert (= (* m m) (- (* (+ n 6) (+ n 6) (+ n 6)) 20)))(check-sat)"""
        cert = self.cert_of(s)
        self.assertEqual(cert['witnesses'], [[0, -14], [0, 14]])
        s = """(declare-fun n () Int)(declare-fun m () Int)
(assert (= (* m m) (- (* (+ n 10) (+ n 10) (+ n 10)) 20)))(check-sat)"""
        self.assertEqual(self.cert_of(s)['witnesses'], [[-4, -14], [-4, 14]])

    def test_replacement_is_equivalent_on_a_box(self):
        # every integer solution with |n| <= 400 is a witness, and conversely
        for r, s_, D in [(3, 15, 56), (1, 0, 20), (2, 1, 5), (1, -2, 1)]:
            text = (f"(declare-fun n () Int)(declare-fun m () Int)(assert (= (* m m) (- (* (+ (* {r} n) {s_}) "
                    f"(+ (* {r} n) {s_}) (+ (* {r} n) {s_})) {D})))(check-sat)")
            cert = self.cert_of(text)
            self.assertIsNotNone(cert, (r, s_, D))
            box = set()
            for n in range(-400, 401):
                v = (r * n + s_) ** 3 - D
                if v >= 0 and isqrt(v) ** 2 == v:
                    box |= {(n, isqrt(v)), (n, -isqrt(v))}
            self.assertEqual({tuple(w) for w in cert['witnesses'] if abs(w[0]) <= 400}, box)

    # -- fail closed
    def test_unsupported_shapes_not_certified(self):
        cases = {
            'singular k = 0': "(declare-fun x () Int)(declare-fun y () Int)(assert (= (* x x) (* y y y)))",
            'div': "(declare-fun n () Int)(declare-fun m () Int)(assert (= (* m m) (+ (* n n n) (div n 2) (- 56))))",
            'or context': "(declare-fun n () Int)(declare-fun m () Int)(declare-fun p () Bool)"
                          "(assert (or p (= (* m m) (- (* n n n) 56))))",
            'not context': "(declare-fun n () Int)(declare-fun m () Int)(assert (not (= (* m m) (- (* n n n) 56))))",
            'let': "(declare-fun n () Int)(declare-fun m () Int)(assert (let ((c (* n n n))) (= (* m m) (- c 56))))",
            'defined symbol': "(declare-fun n () Int)(declare-fun m () Int)(define-fun c () Int (* n n n))"
                              "(assert (= (* m m) (- c 56)))",
            'extension': "(declare-fun n () Int)(declare-fun m () Int)(assert (= (* m m) (int.pow2 n)))",
            'no complete theorem': "(declare-fun n () Int)(declare-fun m () Int)(assert (= (* m m) (- (* n n n) 7)))",
            'three unknowns': "(declare-fun x () Int)(declare-fun y () Int)(declare-fun z () Int)"
                              "(assert (= (+ (* x x x) (* y y y) (* z z z)) 855))",
            'real sort': "(declare-fun n () Real)(declare-fun m () Real)(assert (= (* m m) (- (* n n n) 56)))",
        }
        for why, text in cases.items():
            self.assertIsNone(self.cert_of(text + '(check-sat)'), why)

    def test_no_points_certificate(self):
        text = "(declare-fun n () Int)(declare-fun m () Int)(assert (= (* m m) (+ (* (+ (* 2 n) 1) (+ (* 2 n) 1) (+ (* 2 n) 1)) (- 5))))"
        cert = self.cert_of(text + '(check-sat)')
        self.assertEqual(cert['witnesses'], [])
        self.assertTrue(z3.is_false(self.sc.replacement_formula(cert)))

    def test_script_splitting(self):
        cmds = self.sc.split_commands('; (not a command)\n(set-info :source |a ) b|)(assert (= "x)" "x)"))')
        self.assertEqual(len(cmds), 2)
        with self.assertRaises(ValueError):
            self.sc.split_commands('(assert (= 1 1)')


if __name__ == '__main__':
    unittest.main()
