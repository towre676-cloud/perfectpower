import copy
import io
import json
import pickle
from pathlib import Path
import unittest
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower.elliptic_certificate_verifier import verify_independence
from perfectpower.mordell_cover_charts import projective_cover_lift
from perfectpower.mordell_published_witnesses import (
    _NumericReader, read_published_candidates, augment_published_witnesses,
    recover_cover_preimages, SOURCE_SHA256)

ROOT = Path(__file__).resolve().parents[2]


class PublishedWitnesses(unittest.TestCase):
    def test_five_equations_and_independent_lower_bounds(self):
        receipt = json.loads((ROOT/'receipts/mordell_published_witnesses.json').read_text())
        self.assertEqual(receipt['source_sha256'], SOURCE_SHA256)
        self.assertEqual([r['k'] for r in receipt['rows']], [5935,7482,7823,8210,9454])
        for row in receipt['rows']:
            source = json.loads((ROOT/f"receipts/mordell_two_descent/p{row['k']}.json").read_text())
            E = EllipticCurve([0,row['k']])
            for point in row['points']:
                self.assertIsNotNone(E.checked(point))
                self.assertIn(point,source['points'])
            self.assertTrue(verify_independence(row['independence']))
            self.assertEqual(row['independence'],source['independence'])
            self.assertEqual(source['witness_rank_lower_bound'],1)
            self.assertEqual(source['rank_upper_bound'],1)
            self.assertTrue(source['rank_determined'])
            self.assertEqual(len(row['original_cover_preimages']),1)
            self.assertEqual(recover_cover_preimages(source,row['points'][0]),row['original_cover_preimages'])
            for lift in row['original_cover_preimages']:
                checked = projective_cover_lift(row['k'],source['covers'][lift['cover_index']],lift['coordinates'])
                self.assertEqual(checked['mordell_point'],lift['mordell_point'])
                self.assertIn(lift,source['published_cover_preimages'])

    def test_reject_corruption_and_preserve_scope(self):
        source = json.loads((ROOT/'receipts/mordell_two_descent/p5935.json').read_text())
        replay = augment_published_witnesses(source, source['points'])
        self.assertEqual(replay,source)
        self.assertFalse(replay['integral_point_completeness'])
        self.assertFalse(replay['independence']['complete_basis'])
        original = copy.deepcopy(source)
        with self.assertRaises(ValueError):
            augment_published_witnesses(source,[['0','1']])
        self.assertEqual(source,original)
        wrong_upper = copy.deepcopy(source)
        wrong_upper['rank_upper_bound'] = 0
        with self.assertRaises(ArithmeticError):
            augment_published_witnesses(wrong_upper,source['points'])
        tampered = copy.deepcopy(source['independence'])
        tampered['original_points'][0][1] = '1'
        self.assertFalse(verify_independence(tampered))

    def test_decoder_pinning_and_constructor_allowlist(self):
        with self.assertRaises(ValueError):
            read_published_candidates(b'altered published bytes')
        # A callable outside the two numeric Sage constructors is never loaded.
        class Forbidden:
            def __reduce__(self):
                return (eval,('1+1',))
        with self.assertRaises(ValueError):
            _NumericReader(io.BytesIO(pickle.dumps(Forbidden(),protocol=2))).load()

    def test_zero_gap_ledger_is_backed_by_all_457_packets(self):
        rows = [json.loads(p.read_text()) for p in (ROOT/'receipts/mordell_two_descent').glob('[mp]*.json')]
        self.assertEqual(len(rows),457)
        self.assertTrue(all(r['rank_determined'] and r['witness_rank_lower_bound']==r['rank_upper_bound'] for r in rows))
        self.assertTrue(all(r['integral_point_completeness'] is False for r in rows))
        ledger = json.loads((ROOT/'receipts/mordell_frontier.json').read_text())
        self.assertEqual(ledger['ranks_with_matching_point_witnesses'],457)
        self.assertEqual(ledger['ranks_determined_by_backend_bounds'],457)
        summary = json.loads((ROOT/'receipts/mordell_two_descent/summary.json').read_text())
        self.assertEqual(summary['rank_determined'],457)
        receipt = json.loads((ROOT/'receipts/mordell_published_witnesses.json').read_text())
        self.assertEqual(receipt['frontier_independence_checks'],457)


if __name__=='__main__':
    unittest.main()
