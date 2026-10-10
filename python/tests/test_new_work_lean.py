"""Reject stale or incomplete retained kernel evidence for the recovered work."""
import hashlib,json,re,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]

class RetainedKernelEvidence(unittest.TestCase):
    def test_source_bound_compilation_receipt(self):
        receipt=json.loads((ROOT/'receipts/new_work_lean/verification.json').read_text())
        self.assertTrue(receipt['compiled'])
        self.assertEqual(receipt['lean_version'],'4.20.0')
        for name,digest in receipt['source_sha256'].items():
            self.assertEqual(hashlib.sha256((ROOT/name).read_bytes()).hexdigest(),digest,name)
        records=receipt['declarations']
        self.assertEqual(receipt['declaration_count'],384)
        self.assertEqual(len(records),384)
        audit=(ROOT/'audit/NewWorkClosure.lean').read_text()
        self.assertEqual([r['declaration'] for r in records],re.findall(r'^#print axioms (\S+)',audit,re.M))
        for record in records:
            self.assertLessEqual(set(record['axioms']),{'propext','Classical.choice','Quot.sound'})

    def test_all_future_atlas_exhausts_retained_models(self):
        rows=json.loads((ROOT/'receipts/soe_bridge/all_two_state_automata.json').read_text())
        self.assertEqual(len(rows),324)
        models={json.dumps(r['model'],sort_keys=True) for r in rows}
        self.assertEqual(len(models),324)
        source=(ROOT/'PerfectPower/Generated/SOEModelPackets.lean').read_text()
        self.assertEqual(re.findall(r'^theorem complete(\d+)',source,re.M),[f'{i:03}' for i in range(324)])
        self.assertEqual(source.count('apply SOESemantics.quotient_complete'),324)

if __name__=='__main__':unittest.main()
