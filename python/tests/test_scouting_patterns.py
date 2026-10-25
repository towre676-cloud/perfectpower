import unittest
import numpy as np
import pandas as pd
from perfectpower.scouting_patterns import validate,loss_summary,mechanisms,influence,simultaneous_intervals,exposure_metrics,EXPERTS,matured_role_mean,common_support_contrast
class PatternTests(unittest.TestCase):
    def sample(self):
        rng=np.random.default_rng(44);n=40;y=rng.random(n);b=y+rng.normal(0,.2,n)
        x=pd.DataFrame({'pfr_id':[str(i) for i in range(n)],'draft_year':np.repeat([2023,2024],20),'target':y,'combine':b,'historical':y+.1,'raw':y-.2,'custom':y+.3,'exposure':np.arange(1,n+1)})
        x['aggregate']=x[list(EXPERTS)].mean(axis=1);return x
    def test_paired_gain_and_contributions(self):
        q=self.sample();s=loss_summary(q)
        self.assertAlmostEqual(s['absolute_gain'],s['baseline_mse']-s['candidate_mse']);self.assertAlmostEqual(s['total_loss_reduction'],s['absolute_gain']*len(q))
        self.assertEqual(s['classes'],2)
    def test_two_exact_decompositions(self):
        r=mechanisms(self.sample());self.assertLess(abs(r['diversity_identity_error']),1e-12);self.assertLess(abs(r['correction_identity_error']),1e-12)
        self.assertEqual(set(r['leave_one_expert_out_equal_average_diagnostics']),set(EXPERTS))
    def test_duplicate_and_nonfinite_rejection(self):
        q=self.sample()
        with self.assertRaises(ValueError):validate(pd.concat([q,q]))
        q.loc[0,'raw']=np.nan
        with self.assertRaises(ValueError):validate(q)
    def test_influence_removes_positive_winners_not_losses(self):
        q=self.sample();r,ordered=influence(q);self.assertTrue(ordered.gain.is_monotonic_decreasing)
        for k,v in r['remove_largest_positive_gain_players'].items():self.assertEqual(v['players'],len(q)-int(k));self.assertLess(v['total_loss_reduction'],r['total_gain_sum'])
        self.assertEqual(r['class_sign_flip_sensitivity']['sign_patterns'],4)
    def test_simultaneous_family_and_reproducibility(self):
        q=self.sample();m={'all':(np.ones(len(q),bool),False),'first_class':(q.draft_year.eq(2023).to_numpy(),False),'even':(q.index.to_numpy()%2==0,False)}
        a,info=simultaneous_intervals(q,m,draws=100,seed=3);b,_=simultaneous_intervals(q,m,draws=100,seed=3);self.assertEqual(a,b);self.assertNotIn('first_class',a);self.assertEqual(info['eligible_groups'],2)
        for name,x in a.items():self.assertLessEqual(x['simultaneous_player_95'][0],loss_summary(q.loc[m[name][0]])['absolute_gain']);self.assertGreaterEqual(x['simultaneous_player_95'][1],loss_summary(q.loc[m[name][0]])['absolute_gain'])
    def test_exposure_changes_estimand_and_missing_rejected(self):
        q=self.sample();r=exposure_metrics(q);self.assertEqual(r['players'],len(q));self.assertEqual(r['sum_exposure'],820.)
        q.exposure=np.nan;self.assertEqual(exposure_metrics(q),{'players':0})
    def test_role_control_maturity(self):
        q=self.sample();q['role']='LB';tr=q.rename(columns={'target':'label'}).copy();tr['draft_year']-=2;tr['pfr_id']='training'+tr.pfr_id
        a,audit=matured_role_mean(tr,q);tr.loc[tr.draft_year.eq(2022),'label']=1000
        b,_=matured_role_mean(tr,q);np.testing.assert_array_equal(a[q.draft_year.eq(2023)],b[q.draft_year.eq(2023)])
        self.assertTrue(all(x['latest_training_class']<=x['class']-2 for x in audit))
    def test_common_support_does_not_invent_unmatched_cells(self):
        q=self.sample();q['role']='LB';q['indicator']=q.draft_year.eq(2023);r=common_support_contrast(q,'indicator');self.assertEqual(r['covered_players'],0);self.assertIsNone(r['standardized_positive_minus_negative_gain'])
    def test_class_summary_does_not_call_single_year_replicated(self):
        q=self.sample();self.assertFalse(loss_summary(q[q.draft_year.eq(2023)])['all_observed_classes_positive'])
if __name__=='__main__':unittest.main()
