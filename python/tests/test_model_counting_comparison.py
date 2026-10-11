import unittest
import sys
import tempfile
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'scripts'))
from audit_model_counting_overlap import fingerprint
from compare_model_counting import summarize
from analyze_model_counting_comparison import analyze


class PairedComparisonTests(unittest.TestCase):
    def test_overlap_ignores_relabelled_comments_but_preserves_universe(self):
        with tempfile.TemporaryDirectory() as folder:
            a=Path(folder)/'a.cnf';b=Path(folder)/'b.cnf'
            a.write_text('c 2024\np cnf 3 2\n1 -2 0\n2 3 0\n')
            b.write_text('c 2025\np cnf 3 4\n3 2 0 -2 1 1 0\n1 -1 0\n2 3 0\n')
            self.assertEqual(fingerprint(a),fingerprint(b))
            b.write_text(b.read_text().replace('p cnf 3','p cnf 4'))
            self.assertNotEqual(fingerprint(a),fingerprint(b))

    def test_paired_analysis_keeps_timeouts_in_primary_scores(self):
        def answer(status,seconds):
            return {'status':status,'seconds':seconds,'count':'3' if status=='EXACT' else None}
        receipt={'completed':True,'instances':['a','b'],'repetitions':1,
                 'timeout_seconds':5,'solver_scope':['perfectpower','previous'],
                 'results':[{'name':'a','solvers':{'perfectpower':answer('EXACT',1),'previous':answer('EXACT',2)}},
                            {'name':'b','solvers':{'perfectpower':answer('EXACT',2),'previous':answer('TIMEOUT',5)}}]}
        r=analyze(receipt,'previous',bootstraps=100)
        self.assertEqual(r['coverage_delta'],1)
        self.assertEqual(r['par2_seconds_saved'],9)
        self.assertEqual(r['jointly_solved_instances'],1)
        self.assertEqual(r['jointly_solved_geometric_speedup'],2)
        self.assertEqual(r,analyze(receipt,'previous',bootstraps=100))
        receipt['completed']=False
        with self.assertRaises(ValueError):analyze(receipt,'previous',bootstraps=100)

    def test_denominator_penalties_and_regressions(self):
        def row(name, new, old):
            return {'name': name, 'solvers': {
                'perfectpower': {'status': new, 'seconds': 1},
                'previous': {'status': old, 'seconds': 2}}}
        result = summarize([row('gain', 'EXACT', 'TIMEOUT'),
                            row('loss', 'WORK_LIMIT', 'EXACT'),
                            row('both', 'EXACT', 'EXACT'),
                            row('neither', 'TIMEOUT', 'ERROR')],
                           ['perfectpower', 'previous'], 5)
        self.assertEqual(result['paired_change'], {'gained': ['gain'], 'lost': ['loss']})
        self.assertEqual(result['perfectpower']['par2_seconds'], 22)
        self.assertEqual(result['previous']['par2_seconds'], 24)
        self.assertEqual(sum(result['perfectpower']['outcomes'].values()), 4)
