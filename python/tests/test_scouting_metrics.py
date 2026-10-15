import sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import numpy as np,pandas as pd
from perfectpower.scouting_metrics import physics_features,attach_college,college_box_features,college_event_features,exact_unique,predict,chronological_splits,feature_sets,Design,name_key


class ScoutingMetricsTests(unittest.TestCase):
    def test_height_units_and_physical_proxy(self):
        x=pd.DataFrame({'height_inches':[72.],'wt':[220.],'forty':[4.5],'vertical':[36.],'broad_jump':[120.],'cone':[7.],'shuttle':[4.2],'bench':[20.]})
        z=physics_features(x);self.assertAlmostEqual(z.metric__relative_broad_jump.iloc[0],120/72);self.assertAlmostEqual(z.metric__mean_dash_speed_mps.iloc[0],36.576/4.5)
        x['vertical']=np.nan;self.assertTrue(np.isnan(physics_features(x).metric__vertical_energy_proxy.iloc[0]))
    def test_null_and_ambiguous_identity(self):
        x=pd.DataFrame({'id':[None,'a','b']});self.assertEqual(len(exact_unique(x,['id'],'x')),2)
        with self.assertRaisesRegex(ValueError,'ambiguous'):exact_unique(pd.DataFrame({'id':['a','a']}),['id'],'x')
    def test_college_cutoff_and_missing_lags(self):
        x=pd.DataFrame({'draft_year':[2023],'espn_id':[1]});h=pd.DataFrame({'season':[2021,2022,2023],'athlete_id':[1,1,1],'college_raw__rush_yards':[10.,20.,1e9]})
        out=attach_college(x,h);self.assertEqual(out['college_raw__rush_yards__lag1'].iloc[0],20.);self.assertEqual(out['metric__trend_college_raw__rush_yards'].iloc[0],10.);self.assertTrue(np.isnan(out['college_raw__rush_yards__lag3'].iloc[0]))
    def test_missing_defense_category_stays_unknown(self):
        x=pd.DataFrame({'season':[2022,2022],'game_id':[1,1],'team_id':[3,3],'athlete_id':[4,-1],'category':['receiving','receiving'],'receivingYards':['10','999'],'receptions':['1','99']})
        out=college_box_features(x);self.assertEqual(len(out),1);self.assertTrue(np.isnan(out['college_raw__sacks'].iloc[0]));self.assertEqual(out['metric__college_share_rec_yards'].iloc[0],1.)
    def test_duplicate_box_category_rejected(self):
        x=pd.DataFrame({'season':[2022]*2,'game_id':[1]*2,'team_id':[3]*2,'athlete_id':[4]*2,'category':['receiving']*2})
        with self.assertRaisesRegex(ValueError,'duplicate'):college_box_features(x)
    def test_chronological_gap(self):
        x=pd.DataFrame({'draft_year':np.repeat(range(2013,2020),60)})
        for i,j in chronological_splits(x):self.assertLessEqual(x.iloc[i].draft_year.max(),x.iloc[j].draft_year.min()-2)
    def test_model_ignores_future_labels_and_other_test_players(self):
        rng=np.random.default_rng(57);x=pd.DataFrame({'pfr_id':[str(i) for i in range(130)],'draft_year':[2015]*100+[2017]*30,'pos':'DE','target':rng.normal(size=130),'forty':rng.normal(size=130)})
        a=predict(x.iloc[:100],x.iloc[100:],['forty'],10.);te=x.iloc[100:].copy();te.target=1e8;te.loc[te.index[1:],'forty']=1e8;b=predict(x.iloc[:100],te,['forty'],10.);self.assertEqual(a[0],b[0])
        with self.assertRaisesRegex(ValueError,'maturity'):predict(x.iloc[:100],te.assign(draft_year=2016),['forty'],10.)
    def test_opponent_adjustment_excludes_own_game(self):
        n=42;x=pd.DataFrame({'season':[2022]*n,'game_id':[1]*21+[2]*21,'opponent':['A']*n,'down':[3]*n,'distance':[10]*n,'rush_player_id':[1]*21+[2]*21,'rush_yds':[10]*21+[0]*21,'reception_player_id':[np.nan]*n,'reception_yds':[np.nan]*n,'completion_player_id':[np.nan]*n,'completion_yds':[np.nan]*n})
        out=college_event_features(x).set_index('athlete_id');self.assertEqual(out.loc[1,'metric__rush_opponent_excess'],1.);self.assertEqual(out.loc[2,'metric__rush_opponent_excess'],-1.)
        self.assertGreater(out.loc[1,'metric__rush_success_variance'],0.)
    def test_numeric_id_needs_source_name_verification(self):
        x=pd.DataFrame({'draft_year':[2023],'espn_id':[1],'_join_names':[(name_key('Correct Name Jr.'),)]});h=pd.DataFrame({'season':[2022],'athlete_id':[1],'college_raw__rec_yards':[999.],'_source_name':[name_key('Different Name')]})
        out=attach_college(x,h);self.assertTrue(np.isnan(out['college_raw__rec_yards__lag1'].iloc[0]));self.assertFalse(out['_college_name_verified__lag1'].iloc[0])
    def test_training_support_guard_bounds_new_values(self):
        train=pd.DataFrame({'pos':['WR']*100,'supported':np.arange(100.),'rare':[1.]+[np.nan]*99});d=Design(train,['supported','rare']);a=d.transform(pd.DataFrame({'pos':['WR'],'supported':[1e15],'rare':[1e15]}));b=d.transform(pd.DataFrame({'pos':['WR'],'supported':[1e20],'rare':[-1e20]}));self.assertEqual(a[0,0],b[0,0]);self.assertEqual(a[0,1],0.);self.assertEqual(b[0,1],0.)

if __name__=='__main__':unittest.main()
