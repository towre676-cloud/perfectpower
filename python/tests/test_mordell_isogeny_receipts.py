import json
from pathlib import Path
import unittest
from perfectpower.mordell_three_isogeny import isogeny_point
from perfectpower.mordell_cover_charts import projective_cover_lift
from perfectpower.elliptic_certificate_verifier import verify_independence

ROOT=Path(__file__).resolve().parents[2]


class IsogenyReceipts(unittest.TestCase):
    def test_all_partner_images_reach_original_curves(self):
        folder=ROOT/'receipts/mordell_isogeny_search'
        for path in folder.glob('[mp]*.json'):
            row=json.loads(path.read_text());k=row['k']
            source=json.loads((ROOT/'receipts/mordell_two_descent'/path.name).read_text())
            for run in row['runs']:
                for lift in run['lifts']:
                    partner=projective_cover_lift(-27*k,lift['partner_cover'],lift['partner_coordinates'])
                    self.assertEqual(partner['mordell_point'],lift['partner_point'])
                    self.assertEqual(isogeny_point(k,lift['partner_point'],dual=True),lift['mordell_point'])
                    self.assertIn(lift['mordell_point'],source['points'])
            if source.get('isogeny_point_lifts'):self.assertTrue(verify_independence(source['independence']))

    def test_explicit_second_independent_point_at_9257(self):
        packet=json.loads((ROOT/'receipts/mordell_isogeny_search/rank_two_basis.json').read_text())
        self.assertEqual(packet['k'],-9257);self.assertEqual(packet['points'][0],['21','2'])
        self.assertEqual(len(packet['points']),2);self.assertTrue(verify_independence(packet['independence']))
        self.assertEqual(packet['independence']['rank_lower_bound'],2)
        self.assertFalse(packet['complete_basis'])

    def test_frontier_totals_match_retained_positive_evidence(self):
        rows=[json.loads(p.read_text()) for p in (ROOT/'receipts/mordell_two_descent').glob('[mp]*.json')]
        ledger=json.loads((ROOT/'receipts/mordell_frontier.json').read_text())
        self.assertEqual(ledger['ranks_with_matching_point_witnesses'],sum(r['rank_determined'] for r in rows))
        self.assertTrue(all(r['rank_determined']==(r['witness_rank_lower_bound']==r['rank_upper_bound']) for r in rows))
        self.assertTrue(all(r.get('integral_point_completeness') is False for r in rows))


if __name__=='__main__':unittest.main()
