"""The Why3 consumer bridge (`perfectpower.why3_bridge`).  Text checks need z3-solver; the Why3
runs also need why3 on PATH."""
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
ROOT = Path(__file__).resolve().parents[2]

try:
    import z3  # noqa: F401
except ImportError:
    z3 = None


@unittest.skipIf(z3 is None, 'z3-solver not installed')
class Emission(unittest.TestCase):
    def test_imports_the_parsed_lean_statement(self):
        from perfectpower.why3_bridge import emit
        why, control, meta = emit((ROOT / 'examples' / 'smt' / 'vc_affine56.smt2').read_text())
        self.assertIn('val lemma curve_0 (x y: int) : unit', why)
        self.assertIn('y * y = x * x * x + (-56) <-> (x = 18 /\\ y = (-76)) \\/ (x = 18 /\\ y = 76)', why)
        self.assertIn('let lemma replacement_0', why)
        self.assertIn('(n = 1 /\\ m = (-76)) \\/ (n = 1 /\\ m = 76)', why)
        self.assertNotIn('val lemma', control)
        self.assertNotIn('replacement', control.split('*)', 1)[1])
        self.assertEqual(meta['replacements'][0]['theorem'], 'PerfectPower.Generated.MordellThue.minus56')

    def test_refuses_without_a_checked_replacement(self):
        from perfectpower.why3_bridge import Untranslatable, emit
        with self.assertRaises(Untranslatable):
            emit((ROOT / 'examples' / 'smt' / 'vc_pairs_square.smt2').read_text())
        with self.assertRaises(Untranslatable):
            emit('(declare-const n Int)(declare-const m Int)(assert (> (* m m) (- (* n n n) 56)))(check-sat)')

    @unittest.skipIf(shutil.which('why3') is None, 'why3 not installed')
    def test_why3_accepts_and_control_does_not(self):
        from perfectpower.why3_bridge import emit, run_why3
        why, control, _ = emit((ROOT / 'examples' / 'smt' / 'vc_minus56.smt2').read_text())
        with tempfile.TemporaryDirectory() as d:
            p, q = Path(d) / 'v.mlw', Path(d) / 'c.mlw'
            p.write_text(why)
            q.write_text(control)
            res = run_why3(p, 10)['goals']
            self.assertEqual(res, {'replacement_0': 'Valid', 'vc': 'Valid'})
            self.assertNotEqual(run_why3(q, 5)['goals'].get('vc'), 'Valid')

    @unittest.skipIf(shutil.which('why3') is None, 'why3 not installed')
    def test_wrong_witness_list_is_not_proved(self):
        # a replacement with a dropped sign witness must fail in Why3 (fail closed)
        from perfectpower.why3_bridge import emit, run_why3
        why, _, _ = emit((ROOT / 'examples' / 'smt' / 'vc_minus56.smt2').read_text())
        bad = why.replace('ensures { ((m * m) = ((n * n * n) - 56)) <-> (n = 18 /\\ m = (-76)) \\/ (n = 18 /\\ m = 76) }',
                          'ensures { ((m * m) = ((n * n * n) - 56)) <-> (n = 18 /\\ m = 76) }')
        self.assertNotEqual(bad, why)
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / 'b.mlw'
            p.write_text(bad)
            self.assertNotEqual(run_why3(p, 5)['goals'].get('replacement_0'), 'Valid')


if __name__ == '__main__':
    unittest.main()
