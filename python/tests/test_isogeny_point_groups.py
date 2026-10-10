"""The point-group audit covers every declaration and binds its evidence to source."""
import hashlib
import json
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class IsogenyPointGroups(unittest.TestCase):
    def test_complete_source_bound_kernel_audit(self):
        receipt = json.loads((ROOT/'receipts/isogeny_point_groups/verification.json').read_text())
        self.assertTrue(receipt['compiled'])
        self.assertEqual(receipt['lean_version'], '4.20.0')
        declarations = receipt['declarations']
        self.assertEqual(receipt['declaration_count'], len(declarations))
        self.assertEqual([r['declaration'] for r in declarations],
                         re.findall(r'^#print axioms (\S+)', (ROOT/'audit/IsogenyPointGroups.lean').read_text(), re.M))
        for r in declarations:
            self.assertLessEqual(set(r['axioms']), {'propext', 'Classical.choice', 'Quot.sound'})
        for p, digest in receipt['source_sha256'].items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), digest, p)

    def test_adversarial_sign_and_torsion_controls(self):
        receipt = json.loads((ROOT/'receipts/isogeny_point_groups/verification.json').read_text())
        self.assertEqual(len(receipt['controls']), 5)
        self.assertEqual(sum(r['accepted'] for r in receipt['controls']), 2)
        for r in receipt['controls']:
            self.assertEqual(r['accepted'], r['expected_acceptance'])


if __name__ == '__main__':
    unittest.main()
