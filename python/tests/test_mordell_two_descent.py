import copy,json,os,shutil,unittest
from pathlib import Path
from perfectpower.elliptic_two_descent import cubic_order,quartic_map,lift_quartic_point,mordell_two_descent
from perfectpower.elliptic_certificate_verifier import verify_independence
from perfectpower.cubic_norm_transport import binary_cubic_norm,recover_binary_coordinates

ROOT=Path(__file__).resolve().parents[2]


class DescentArithmetic(unittest.TestCase):
    def test_all_committed_covers_orders_and_point_lower_bounds(self):
        files=sorted((ROOT/'receipts/mordell_two_descent').glob('[mp]*.json'))
        self.assertEqual(len(files),457)
        covers=0
        for path in files:
            c=json.loads(path.read_text());field=c['field']
            self.assertEqual(field['nfcertify'],[])
            for cover in c['covers']:self.assertTrue(quartic_map(c['k'],cover));covers+=1
            computed=cubic_order(field['polynomial'],field['integral_basis'],field['discriminant'])
            for key,value in computed.items():self.assertEqual(field[key],value)
            self.assertEqual(c['rank_upper_bound'],len(c['covers'])-c['cassels_removed_dimension'])
            self.assertTrue(verify_independence(c['independence']))
            self.assertEqual(c['witness_rank_lower_bound'],c['independence']['rank_lower_bound'])
        self.assertEqual(covers,1027)

    def test_changed_cover_and_discriminant_are_rejected(self):
        c=json.loads((ROOT/'receipts/mordell_two_descent/m9955.json').read_text())
        cover=copy.deepcopy(c['covers'][0]);cover['x_numerator'][0]='1'
        with self.assertRaises(ValueError):quartic_map(c['k'],cover)
        field=c['field']
        with self.assertRaises(ValueError):cubic_order(field['polynomial'],field['integral_basis'],field['discriminant']+1)

    def test_affine_cover_lift(self):
        # The identity map on the degree-three genus-one chart: N_x=t R, N_y=R^2.
        cover=dict(quartic=['-2','0','0','1'],x_numerator=['0','-2','0','0','1'],
                   y_numerator=['4','0','0','-4','0','0','1'])
        self.assertEqual(lift_quartic_point(-2,cover,[3,5]),['3','5'])
        with self.assertRaises(ValueError):lift_quartic_point(-2,cover,[3,4])

    def test_nonmonic_signed_transport_and_domain(self):
        for a in (-7,-2,1,3,11):
            coefficients=[-5,3,-2,a]
            for r in range(-4,5):
                for s in range(-4,5):
                    c=binary_cubic_norm(coefficients,r,s)
                    self.assertEqual(c['norm'],a*a*c['source_value'])
                    self.assertEqual(recover_binary_coordinates(coefficients,c['element']),[r,s])
        with self.assertRaises(ValueError):recover_binary_coordinates([-5,3,-2,3],[1,1,0])
        with self.assertRaises(ValueError):recover_binary_coordinates([-5,3,-2,3],[3,1,1])

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_GP') or shutil.which('gp'),'optional PARI/GP')
    def test_live_general_descent(self):
        c=mordell_two_descent(-9955,[['7891/361','151704/6859']])
        self.assertEqual((c['selmer_dimension'],c['cassels_removed_dimension'],c['rank_upper_bound']),(3,2,1))
        self.assertTrue(c['rank_determined'])
        self.assertEqual(c['field']['power_order_index'],3)
        self.assertFalse(c['integral_point_completeness'])

    def test_invalid_controls(self):
        for k in (True,0,-8,10**10):
            with self.assertRaises(ValueError):mordell_two_descent(k)
        with self.assertRaises(ValueError):mordell_two_descent(-2,effort=True)

    def test_frontier_corrections_do_not_promote_integral_lists(self):
        c=json.loads((ROOT/'receipts/mordell_frontier.json').read_text())
        self.assertEqual(c['remaining_count'],457)
        search=json.loads((ROOT/'receipts/mordell_cover_search.json').read_text())
        self.assertEqual(c['ranks_determined_by_two_descent'],289+len(search['newly_determined']))
        self.assertEqual(len(c['census_rank_corrections']),11)
        self.assertTrue(all(row['census_rank']==1 and row['proved_rank']==2 for row in c['census_rank_corrections']))


if __name__=='__main__':unittest.main()
