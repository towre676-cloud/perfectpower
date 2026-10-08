import copy,json,unittest
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower.mordell_completion import accept_completion,subgroup_index,verify_completion_log
from perfectpower.elliptic_reduction_saturation import reduction_saturation,replay_reduction_saturation,finite_group,add,multiply

ROOT=Path(__file__).resolve().parents[2]


class MordellCompletion(unittest.TestCase):
    def test_all_457_completed_bases_and_integral_lists(self):
        packets=[json.loads(p.read_text()) for p in (ROOT/'receipts/mordell_completion').glob('[mp][0-9]*.json')]
        self.assertEqual(len(packets),457)
        checks=0
        for p in packets:
            source=json.loads((ROOT/p['source_descent']).read_text())
            self.assertTrue(verify_completion_log(p,(ROOT/p['source_descent'].replace('mordell_two_descent','mordell_completion')).with_suffix('.log').read_text()))
            self.assertTrue(accept_completion(p,source),p['k'])
            self.assertEqual(p['source_subgroup_index'],1)
            checks+=len(p['exact_prime_saturation'])
        self.assertEqual(checks,788)
        self.assertEqual(sum(len(p['integral_points']) for p in packets),270)
        self.assertEqual(sum(not p['x_coordinates'] for p in packets),323)

    def test_mutations_cannot_promote_partial_or_wrong_results(self):
        p=json.loads((ROOT/'receipts/mordell_completion/p5935.json').read_text())
        source=json.loads((ROOT/p['source_descent']).read_text())
        for key,value in [('saturation_max_prime',13),('backend_saturation_ok',False),
                          ('unsaturated_primes',[17]),('original_to_basis',[[2]]),
                          ('integral_points',[['0','1']]),('lean_integral_list_proved',True)]:
            changed=copy.deepcopy(p);changed[key]=value
            self.assertFalse(accept_completion(changed,source),key)
        changed=copy.deepcopy(p);changed['exact_prime_saturation'][0]['reductions'][0]['group_order']+=1
        self.assertFalse(accept_completion(changed,source))
        changed=copy.deepcopy(p);changed['exact_prime_saturation']=[];changed['backend_required_saturation_primes']=[]
        self.assertFalse(accept_completion(changed,source))
        self.assertFalse(verify_completion_log(p,'changed backend output'))

    def test_finite_reductions_distinguish_a_generator_from_a_multiple(self):
        E=EllipticCurve([0,-2]);P=['3','5'];triple=E.point_multiply(P,3)
        self.assertTrue(reduction_saturation(-2,[P],3,97)['independent_mod_prime'])
        failed=reduction_saturation(-2,[triple],3,97)
        self.assertFalse(failed['independent_mod_prime'])
        self.assertEqual(failed['surviving_lines'],[[1]])
        self.assertFalse(replay_reduction_saturation(failed))
        dependent=reduction_saturation(-2,[P,P],3,97)
        self.assertIn([1,2],dependent['surviving_lines'])
        self.assertFalse(dependent['independent_mod_prime'])
        # Independent direct group-law checks on the complete finite set.
        group=finite_group(-2%7,7)
        self.assertEqual(len(group),7)
        for point in group:
            self.assertIn(add(7,point,point),group)
            self.assertIsNone(multiply(7,point,7))

    def test_redundant_rank_two_relations_have_the_correct_index(self):
        self.assertEqual(subgroup_index([[1,0],[0,1],[3,-1]],2),1)
        self.assertEqual(subgroup_index([[2,0],[0,3]],2),6)
        p=json.loads((ROOT/'receipts/mordell_completion/m9257.json').read_text())
        self.assertEqual(p['original_to_basis'],[[1,0],[0,1],[3,-1]])
        self.assertEqual(p['x_coordinates'],[21])

    def test_published_census_and_current_frontier_agree(self):
        cross=json.loads((ROOT/'receipts/mordell_completion/published_integral_crosscheck.json').read_text())
        self.assertEqual(cross['curves_compared'],457);self.assertEqual(cross['mismatches'],[])
        for row in cross['rows']:
            p=json.loads((ROOT/f'receipts/mordell_completion/{"m" if row["k"]<0 else "p"}{abs(row["k"])}.json').read_text())
            self.assertEqual(sorted(row['published_integral_points']),sorted([list(map(int,xy)) for xy in p['integral_points']]))
        frontier=json.loads((ROOT/'receipts/mordell_frontier.json').read_text())
        self.assertEqual(frontier['remaining_count'],0)
        self.assertEqual(frontier['external_computation_list_closure_count'],457)
        self.assertEqual(frontier['rank_witness_frontier_count'],457)
        self.assertEqual(frontier['ranks_with_matching_point_witnesses'],457)


if __name__=='__main__':unittest.main()
