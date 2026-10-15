import unittest
import numpy as np
import pandas as pd
from perfectpower.scouting_identity import strict_name,birth,roster_identity,contextual_recruits,available_before,delayed_aggregate,recruitment_residual,EXPERTS

class IdentityTests(unittest.TestCase):
    def roster(self):
        return pd.DataFrame([dict(season=2018,athlete_id=1,team_id=2,athlete_display_name='John Smith',full_name='John Smith',date_of_birth='1997-01-01')])
    def prospects(self):
        return pd.DataFrame([dict(pfr_id='s',draft_year=2019,pos='WR',espn_id=99,birth_date='1997-01-01',player_name='John Smith',display_name='John Smith')])
    def recruits(self):
        return pd.DataFrame([dict(season=2018,recruit_id='1',team_id='2',player_name='John Smith',stars=3.,grade=85.)])
    def test_names_preserve_suffix(self):
        self.assertNotEqual(strict_name('John Smith Jr.'),strict_name('John Smith'))
        self.assertEqual(strict_name('André Dillard'),strict_name('Andre Dillard'))
        self.assertIsNone(birth('1997-02-31'))
    def test_birth_bridge_and_ambiguity(self):
        r=self.roster();p=self.prospects();self.assertEqual(roster_identity(p,r).iloc[0].college_id,1)
        r=pd.concat([r,r.assign(athlete_id=3)]);q=roster_identity(p,r).iloc[0]
        self.assertEqual(q.status,'ambiguous');self.assertIsNone(q.college_id)
    def test_conflicting_births_and_reciprocal_identity_rejected(self):
        r=self.roster();p=self.prospects()
        self.assertEqual(roster_identity(p,pd.concat([r,r.assign(date_of_birth='1997-02-02')])).iloc[0].status,'unsupported')
        p=pd.concat([p,p.assign(pfr_id='other')]);self.assertTrue(roster_identity(p,r).status.eq('ambiguous').all())
    def test_future_and_wrong_birth_do_not_rescue(self):
        p=self.prospects();r=self.roster();self.assertEqual(roster_identity(p,r.assign(season=2019)).iloc[0].status,'unsupported')
        self.assertEqual(roster_identity(p,r.assign(date_of_birth='1997-01-02')).iloc[0].status,'unsupported')
    def test_numeric_namespace_not_a_link(self):
        r=self.roster();q=self.recruits().assign(player_name='Different Person')
        self.assertEqual(contextual_recruits(q,r).iloc[0].status,'no_context_match')
    def test_context_and_wrong_school(self):
        self.assertEqual(contextual_recruits(self.recruits(),self.roster()).iloc[0].status,'corroborated_context_only')
        self.assertEqual(contextual_recruits(self.recruits().assign(team_id='3'),self.roster()).iloc[0].status,'no_context_match')
    def test_earlier_enrollment_and_many_to_one(self):
        r=self.roster();q=self.recruits()
        self.assertEqual(contextual_recruits(q,pd.concat([r,r.assign(season=2017)])).iloc[0].status,'earlier_enrollment_conflict')
        q=pd.concat([q,q.assign(recruit_id='4')]);self.assertTrue(contextual_recruits(q,r).status.eq('nonunique_recruit_history').all())
    def test_duplicate_recruit_source_rejected(self):
        q=self.recruits()
        with self.assertRaises(ValueError):contextual_recruits(pd.concat([q,q]),self.roster())
    def test_asof_fails_closed(self):
        self.assertFalse(available_before(None,'2019-04-25T00:00Z',True))
        self.assertFalse(available_before('2018-01-01','2019-04-25T00:00Z',True))
        self.assertFalse(available_before('2020-01-01T00:00Z','2019-04-25T00:00Z',True))
        self.assertFalse(available_before('2018-01-01T00:00Z','2019-04-25T00:00Z',False))
        self.assertTrue(available_before('2018-01-01T00:00Z','2019-04-25T00:00Z',True))
    def predictions(self):
        return pd.DataFrame([dict(pfr_id=str(i),draft_year=2018+i,target=.4,combine=.3,historical=.4,raw=.5,custom=.6) for i in range(8)])
    def test_future_outcomes_cannot_change_past(self):
        q=self.predictions();a,w=delayed_aggregate(q,1.);q.loc[q.draft_year.ge(2021),'target']=100
        b,z=delayed_aggregate(q,1.);np.testing.assert_array_equal(a.loc[a.draft_year.le(2022),'aggregate'],b.loc[b.draft_year.le(2022),'aggregate'])
        for row in w:self.assertTrue(all(y<=row['class']-2 for y in row['history_classes']))
    def test_convexity_and_regret(self):
        rng=np.random.default_rng(17);q=self.predictions();q[['target',*EXPERTS]]=rng.random((len(q),5));r,w=delayed_aggregate(q,1.)
        self.assertTrue((r['aggregate']>=r[list(EXPERTS)].min(axis=1)).all());self.assertTrue((r['aggregate']<=r[list(EXPERTS)].max(axis=1)).all())
        for parity in (0,1):
            g=r[r.draft_year%2==parity];loss=((g.target-g['aggregate'])**2).sum();best=min(((g.target-g[e])**2).sum() for e in EXPERTS)
            self.assertLessEqual(loss-best,np.log(4)+len(g)/8)
    def test_bad_predictions_rejected(self):
        q=self.predictions()
        with self.assertRaises(ValueError):delayed_aggregate(pd.concat([q,q]),1.)
        q.loc[0,'raw']=np.nan
        with self.assertRaises(ValueError):delayed_aggregate(q,1.)
    def test_no_eligible_recruitment_no_residual(self):
        with self.assertRaises(ValueError):recruitment_residual(np.arange(30),np.arange(30),np.ones(30,bool),np.zeros(30,bool))

if __name__=='__main__':unittest.main()
