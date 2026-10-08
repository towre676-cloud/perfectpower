"""Check that retained frontier claims reach the original arithmetic objects."""
import json
from pathlib import Path
import unittest
from perfectpower.elliptic_certificate_verifier import verify_independence
from perfectpower.mordell_cover_search import affine_homogeneous_lift
from perfectpower.mordell_cover_charts import chart_cover

ROOT=Path(__file__).resolve().parents[2]


class FrontierReceipts(unittest.TestCase):
    def test_contraction_atlas_covers_every_retained_cover(self):
        atlas=json.loads((ROOT/'receipts/quartic_invariants/contraction_atlas.json').read_text())
        expected={(r['k'],i) for path in (ROOT/'receipts/mordell_two_descent').glob('[mp]*.json')
                  for r in [json.loads(path.read_text())] for i in range(len(r['covers']))}
        actual=[(r['k'],r['cover_index']) for r in atlas['rows']]
        self.assertEqual(set(actual),expected);self.assertEqual(len(actual),len(expected))
        self.assertFalse(atlas['invariants_establish_equivalence'])

    def test_all_reduced_models_retain_the_original_maps(self):
        for path in (ROOT/'receipts/quartic_invariants').glob('[mp]*.json'):
            row=json.loads(path.read_text())
            source=json.loads((ROOT/'receipts/mordell_two_descent'/path.name).read_text())
            for i,model in enumerate(row['models']):
                chart=model['chart'];self.assertEqual(chart['source_cover'],source['covers'][i])
                self.assertEqual(chart,chart_cover(row['k'],source['covers'][i],chart['matrix'],chart['ordinate_scale']))

    def test_new_witness_claims_have_exact_independence_and_lifts(self):
        frontier=json.loads((ROOT/'receipts/quartic_invariants/frontier.json').read_text())
        for k in {k for run in frontier['runs'] for k in run['newly_closed']}:
            name=('m' if k<0 else 'p')+str(abs(k))+'.json'
            packet=json.loads((ROOT/'receipts/mordell_two_descent'/name).read_text())
            self.assertTrue(verify_independence(packet['independence']))
            self.assertEqual(packet['witness_rank_lower_bound'],packet['rank_upper_bound'])
            self.assertTrue(packet['cover_point_lifts'])
            for record in packet['cover_point_lifts']:
                lift=affine_homogeneous_lift(k,packet['covers'][record['cover_index']],record['cover_point'])
                self.assertEqual(lift['mordell_point'],record['mordell_point'])
                self.assertEqual(lift,record['homogeneous'])


if __name__=='__main__':unittest.main()
