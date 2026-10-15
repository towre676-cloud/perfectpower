import sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import numpy as np,pandas as pd
from perfectpower.scouting_depth import aggregate_usage,attach_usage,fit_predict,RAW_USAGE,resolve_college_ids


class ScoutingDepthTests(unittest.TestCase):
    def test_cross_namespace_bridge_needs_exact_birth_name_and_unique_predraft_id(self):
        rows=pd.DataFrame({'draft_year':[2023]*3,'espn_id':[17]*3,'birth_date':['2000-01-01']*3,'_join_names':[('rightname',),('different',),('ambiguous',)]})
        roster=pd.DataFrame({'season':[2022,2023,2022,2022],'athlete_id':[22,99,33,44],'athlete_display_name':['Right Name','Right Name','Ambiguous','Ambiguous'],'full_name':['Right Name']*4,'date_of_birth':['2000-01-01T00:00Z']*4})
        out,audit=resolve_college_ids(rows,roster);self.assertEqual(out.espn_id.tolist(),[22,17,17]);self.assertEqual(audit['new_namespace_links'],1);self.assertEqual(audit['ambiguous_birth_name_links'],1)
    def usage(self):
        row={c:0. for c in RAW_USAGE};row.update(season=2022,player_id='17',player_name='Exact Name',pos_team_id=1,targets=10.,receptions=0.,opportunities=10.,games=2.,team_targets=100.,team_touches=150.)
        return pd.DataFrame([row])
    def test_incomplete_targets_remain_opportunities(self):
        out=aggregate_usage(self.usage(),'offense').iloc[0]
        self.assertEqual(out.depth_metric__offense_yards_per_target,0.)
        self.assertEqual(out.depth_metric__offense_target_share,.1)
        self.assertEqual(out.depth_raw__offense_targets,10.)
    def test_transfer_counts_sum_without_duplicate_identity(self):
        x=self.usage();second=x.assign(pos_team_id=2,targets=5.,opportunities=5.)
        z=aggregate_usage(pd.concat([x,second]),'offense').iloc[0];self.assertEqual(z.depth_raw__offense_targets,15.)
        with self.assertRaisesRegex(ValueError,'duplicate'):aggregate_usage(pd.concat([x,x]),'offense')
    def test_id_alone_and_draft_season_cannot_enter(self):
        h=aggregate_usage(self.usage(),'offense');u=pd.DataFrame({'draft_year':[2023,2023,2022],'espn_id':[17]*3,'_join_names':[('exactname',),('othername',),('exactname',)]})
        out,audit=attach_usage(u,h,'offense');c='depth_raw__offense_targets__lag1'
        self.assertEqual(out[c].iloc[0],10.);self.assertTrue(np.isnan(out[c].iloc[1]));self.assertTrue(np.isnan(out[c].iloc[2]))
    def test_models_are_player_and_time_separated_and_test_label_blind(self):
        rng=np.random.default_rng(51);tr=pd.DataFrame({'pfr_id':[str(i) for i in range(110)],'draft_year':2015,'pos':['WR']*55+['TE']*55,'x':rng.normal(size=110),'target':rng.normal(5,1,110)})
        te=tr.iloc[:2].assign(pfr_id=['new1','new2'],draft_year=2017)
        for spec in [('ridge',100.),('role_ridge',100.),('boost',2,1.)]:
            a=fit_predict(tr,te,['x'],spec);b=fit_predict(tr,te.assign(target=1e10),['x'],spec);np.testing.assert_equal(a,b)
            with self.assertRaisesRegex(ValueError,'player'):fit_predict(tr,tr,['x'],spec)
            with self.assertRaisesRegex(ValueError,'maturity'):fit_predict(tr,te.assign(draft_year=2016),['x'],spec)


if __name__=='__main__':unittest.main()
