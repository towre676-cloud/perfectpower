import gzip,json,unittest
from pathlib import Path
from flint import arb
from perfectpower.wall_profile_intervals import seed_nodes,check_seed,generate_declared_seed
from perfectpower.wall_stability_certified import certify_gap
ROOT=Path(__file__).resolve().parents[2]


class DeclaredWallTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path=ROOT/'receipts/flavor_cosmology/wall_declared_interval_seed.json.gz'
        cls.seed=json.loads(gzip.decompress(path.read_bytes())) if path.exists() else generate_declared_seed()
        cls.result=certify_gap(cls.seed,coercivity='0.0001',radius_ball='0.00005')

    def test_declared_gap_and_translation_kernel(self):
        self.assertEqual(self.seed['parameters']['lambda'],'0.1')
        a=self.result['bounds_Arb']
        self.assertTrue(arb(a['gap_GeV_lower'])>124.40)
        self.assertTrue(arb(a['gap_GeV_lower'])<125.44)
        self.assertTrue(self.result['kernel_is_translation_only_certified'])

    def test_receipt_and_independent_precision_overlap(self):
        out=json.loads((ROOT/'receipts/flavor_cosmology/wall_declared_stability_certified.json').read_text())
        self.assertEqual(out['radial_gap']['bounds_Arb'],self.result['bounds_Arb'])
        for k,v in self.result['bounds_Arb'].items():self.assertTrue(arb(v).overlaps(arb(out['replay_192_bits'][k])),k)
        self.assertFalse(out['angular_Higgs_sector']['strict_positive_gap_claimed'])

    def test_bad_mesh_and_overlarge_coercivity_rejected(self):
        bad=dict(self.seed,nodes_hex=list(self.seed['nodes_hex']));bad['nodes_hex'][2]=bad['nodes_hex'][1]
        with self.assertRaises(ValueError):seed_nodes(bad)
        with self.assertRaises(ValueError):check_seed(self.seed,coercivity='0')
        with self.assertRaises(ArithmeticError):check_seed(self.seed,coercivity='0.5')


if __name__=='__main__':unittest.main()
