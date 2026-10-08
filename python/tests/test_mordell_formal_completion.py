import hashlib,json,unittest
from pathlib import Path
from reconcile_mordell_formal_completion import audited_declarations

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'receipts/mordell_formal_completion'


class FormalCompletionBoundary(unittest.TestCase):
    def test_actual_audit_and_source_identities(self):
        packet=json.loads((OUT/'status.json').read_text())
        names=audited_declarations((OUT/'axioms.log').read_text())
        self.assertEqual(len(names),10)
        self.assertEqual(packet['audited_declarations'],names)
        for name,digest in packet['source_sha256'].items():
            self.assertEqual(hashlib.sha256((ROOT/name).read_bytes()).hexdigest(),digest)
        for name,digest in packet['log_sha256'].items():
            self.assertEqual(hashlib.sha256((OUT/name).read_bytes()).hexdigest(),digest)

    def test_unproved_curve_inputs_are_not_promoted(self):
        p=json.loads((OUT/'status.json').read_text())
        self.assertEqual(p['formally_completed_curves'],0)
        self.assertEqual(len(p['rows']),457)
        for row in p['rows']:
            self.assertFalse(row['lean_complete_basis_proved'])
            self.assertFalse(row['lean_integral_list_proved'])
            for key in ['global_saturation_prime_support','rank_upper_bound','global_integral_coordinate_bound']:
                self.assertEqual(row[key],'unproved in Lean')

    def test_unsafe_or_partial_axiom_reports_are_rejected(self):
        log=(OUT/'axioms.log').read_text()
        for changed in [log+'\nerror: failed',log.replace('Quot.sound','sorryAx'),
                        log.replace('Quot.sound','CustomGlobalCompleteness'),
                        log.replace('Quot.sound','Lean.ofReduceBool')]:
            with self.assertRaises(ValueError):audited_declarations(changed)

    def test_missing_theorem_audit_is_rejected(self):
        log=(OUT/'axioms.log').read_text()
        changed=log.replace("'PerfectPower.MordellCompletionBridge.integralList_complete'","'Other.unrelated'")
        with self.assertRaises(ValueError):audited_declarations(changed)


if __name__=='__main__':unittest.main()
