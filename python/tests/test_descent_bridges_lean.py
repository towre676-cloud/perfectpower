"""Source-bound kernel evidence and exact retained arithmetic-corpus coverage."""
import hashlib,json,re,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]

class DescentKernelEvidence(unittest.TestCase):
    def test_source_bound_audit(self):
        receipt=json.loads((ROOT/'receipts/descent_bridges/verification.json').read_text())
        self.assertTrue(receipt['compiled'])
        self.assertEqual(receipt['lean_version'],'4.20.0')
        for name,digest in receipt['source_sha256'].items():
            self.assertEqual(hashlib.sha256((ROOT/name).read_bytes()).hexdigest(),digest,name)
        records=receipt['declarations']
        self.assertEqual(receipt['declaration_count'],len(records))
        audit=(ROOT/'audit/DescentBridges.lean').read_text()
        self.assertEqual([r['declaration'] for r in records],re.findall(r'^#print axioms (\S+)',audit,re.M))
        for r in records:
            self.assertLessEqual(set(r['axioms']),{'propext','Classical.choice','Quot.sound'})

    def test_rejection_controls(self):
        receipt=json.loads((ROOT/'receipts/descent_bridges/rejections/verification.json').read_text())
        self.assertEqual(len(receipt['cases']),6)
        self.assertEqual(sum(not c['accepted'] for c in receipt['cases']),4)
        for c in receipt['cases']:self.assertEqual(c['accepted'],c['expected_acceptance'])
        for name,digest in receipt['source_sha256'].items():
            self.assertEqual(hashlib.sha256((ROOT/name).read_bytes()).hexdigest(),digest,name)

    def test_retained_exclusions_and_models_complete(self):
        rows=json.loads((ROOT/'receipts/structural_math/two_isogeny_corpus.json').read_text())
        instances=json.loads((ROOT/'receipts/descent_bridges/instances.json').read_text())
        excluded={tuple(c['cover']) for row in rows for side in ('left','right')
                  for c in row[side]['classes'] if c['status']=='excluded'}
        self.assertEqual({tuple(c['cover']) for c in instances['covers']},excluded)
        self.assertEqual(len(instances['covers']),1478)
        models={tuple(row[side]['curve']):row[side]['survivors'] for row in rows for side in ('left','right')}
        self.assertEqual({tuple(c['curve']):c['survivors'] for c in instances['models']},models)
        self.assertEqual(len(instances['models']),576)
        for c in instances['covers']:
            self.assertIn(f"theorem cover_{c['index']:04d} ",(ROOT/c['module']).read_text())
        for c in instances['models']:
            self.assertIn(f"theorem model_{c['index']:04d}_rational_cover ",(ROOT/c['module']).read_text())

if __name__=='__main__':unittest.main()
