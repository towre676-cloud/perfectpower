"""The guarded unsigned-bitvector adapter (`perfectpower.unsigned_adapter`) on the independently
authored Why3 Von Neumann isqrt VCs (`why3_isqrt/`).  Skipped when z3-solver is not installed."""
import copy, json, pathlib, re, sys, unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'python'))
try:
    import z3
    from perfectpower.unsigned_adapter import derive, check, accelerate
except ImportError:  # optional dependency
    z3 = None

W = ROOT / 'why3_isqrt'
REAL = W / 'raw_bv_vcs' / 'isqrt_von_neumann-VonNeumann64-isqrt64qtvc26.smt2'

def task(guard=True,w=8):
    h='(assert (bvule b n))' if guard else ''
    return f'''(set-logic QF_BV)
    (declare-fun n () (_ BitVec {w})) (declare-fun b () (_ BitVec {w}))
    (declare-fun x () (_ BitVec {w}))
    {h} (assert (bvule n x))
    (assert (not (bvule (bvsub n b) x))) (check-sat)'''

@unittest.skipIf(z3 is None, 'z3-solver not installed')
class Tests(unittest.TestCase):
    def test_real_certificate(self):
        t=REAL.read_text();c=derive(t);self.assertTrue(check(t,c));self.assertGreater(len(c['steps']),0)
    def test_all_exhaustive_small_words(self):
        for w in range(8):
            for n in range(1<<w):
                for b in range(n+1):self.assertLessEqual((n-b)%max(1,1<<w),n)
    def test_guard_is_essential(self):
        t=task(False);out,c=accelerate(t)
        self.assertEqual(t,out);self.assertFalse(check(t,c))
        s=z3.Solver();s.add(*z3.parse_smt2_string(out));self.assertEqual(s.check(),z3.sat)
    def test_valid_unsat(self):
        for w in [1,2,8,16,32,64,128]:
            t=task(True,w);out,c=accelerate(t);self.assertTrue(check(t,c))
            s=z3.Solver();s.add(*z3.parse_smt2_string(out));self.assertEqual(s.check(),z3.unsat)
    def test_each_step_field_mutation_rejected(self):
        t=REAL.read_text();base=derive(t)
        for field in ['width','n','b','x','fact','term_assertion','guard_assertion','upper_assertion']:
            c=copy.deepcopy(base);v=c['steps'][0][field]
            c['steps'][0][field]=(v+1 if isinstance(v,int) else 'FORGED')
            self.assertFalse(check(t,c),field)
    def test_source_mutation_rejected(self):
        t=REAL.read_text();c=derive(t);self.assertFalse(check(t+'\n;changed\n',c))
    def test_incremental_scopes_rejected(self):
        for extra in ['(push 1)','(pop 1)','(reset)','(check-sat)']:
            with self.assertRaises(ValueError):derive(extra+'\n'+task())
    def test_no_unsigned_reinterpretation(self):
        t=task().replace('(bvule b n)','(bvsle b n)')
        c=derive(t);self.assertFalse(check(t,c))
    def test_aliases_are_not_assumed(self):
        t=task().replace('(bvule b n)','(bvule n b)')
        # There may be bounds for different subtractions, but this goal has no valid guard.
        out,c=accelerate(t);self.assertEqual(t,out)
    def test_cross_context_not_combined(self):
        with self.assertRaises(ValueError):derive(task()+'\n(push 1)\n(check-sat)')
    def test_future_assertion_not_used(self):
        with self.assertRaises(ValueError):derive(task(False)+'\n(assert (bvule b n))')
    def test_reset_assertions_rejected(self):
        with self.assertRaises(ValueError):derive('(reset-assertions)\n'+task())
    def test_command_looking_strings_do_not_create_queries(self):
        t='(set-info :source "fake (check-sat); still a string")\n'+task()
        out,c=accelerate(t);self.assertTrue(check(t,c));self.assertIn(':source',out)
    def test_comment_looking_quoted_symbol_is_not_removed(self):
        t=re.sub(r'\bn\b','|n;not-comment|',task())
        out,c=accelerate(t);self.assertTrue(check(t,c));self.assertIn('|n;not-comment|',out)
    def test_policy_keeps_irrelevant_assertions_intact(self):
        t=task().replace('(not (bvule (bvsub n b) x))','(not (= (bvsub n b) x))')
        out,c=accelerate(t);self.assertEqual(t,out);self.assertEqual(c['steps'],[])
    def test_buggy_program_ground_slice_remains_satisfiable(self):
        t=(W/'negative_controls'/'buggy_terminal64_ground.smt2').read_text()
        out,c=accelerate(t);self.assertTrue(check(t,c))
        s=z3.Solver();s.add(*z3.parse_smt2_string(out));self.assertEqual(s.check(),z3.sat)

    def test_all_307_instances_recheck(self):
        n = 0
        for p in sorted((W / 'raw_bv_vcs').glob('*.smt2')):
            t = p.read_text(); c = derive(t)
            if c['steps']:
                self.assertTrue(check(t, c)); n += len(c['steps'])
        self.assertEqual(n, 307)
        lean = (ROOT / 'PerfectPower' / 'Generated' / 'WorkflowInstances.lean').read_text()
        self.assertEqual(lean.count('\ntheorem '), 307)


if __name__=='__main__':unittest.main()
