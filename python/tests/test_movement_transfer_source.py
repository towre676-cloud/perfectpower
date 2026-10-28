"""Source-vintage metadata guards; synthetic data never substitutes football data."""
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import numpy as np
import pandas as pd

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'scripts'))
from run_movement_transfer import PHYS,extract,model_predict,source_metadata


def players(n=20):
    rng=np.random.default_rng(1881)
    q=pd.DataFrame({c:rng.normal(size=n) for c in PHYS})
    q['nfl_id']=np.arange(n);q['draft_year']=2024
    q['combine_position']=np.where(q.nfl_id%2,'DE','LB')
    q['target']=np.clip(.1+.01*q.forty,0,1)
    return q


class SourceMetadata(unittest.TestCase):
    def test_source_position_required_without_nfl_fallback(self):
        q=players();q['nfl_position']='DE'
        with self.assertRaisesRegex(ValueError,'combine_position'):
            source_metadata(q.drop(columns='combine_position'))
        with self.assertRaisesRegex(ValueError,'combine_position'):
            model_predict(q.iloc[:15].drop(columns='combine_position'),q.iloc[15:],[],10,0)

    def test_missing_numeric_values_permitted_and_order_invariant(self):
        q=players(3);q.loc[0,'forty']=np.nan
        repeated=pd.concat([q,q],ignore_index=True)
        repeated.loc[3,'combine_height']=np.nan
        a=source_metadata(repeated);b=source_metadata(repeated.sample(frac=1,random_state=42))
        pd.testing.assert_frame_equal(a,b)
        self.assertTrue(np.isnan(a.loc[0,'forty']))
        self.assertEqual(a.loc[0,'combine_height'],q.loc[0,'combine_height'])

    def test_conflicting_measurement_or_source_position_rejected(self):
        q=players(3);q=pd.concat([q,q.iloc[:1]],ignore_index=True)
        for field,value in [('forty',99.),('combine_position','DT')]:
            bad=q.copy();bad.loc[len(bad)-1,field]=value
            with self.assertRaisesRegex(ValueError,field):source_metadata(bad)

    def test_invalid_identity_or_numeric_evidence_rejected(self):
        q=players(3)
        for col,value in [('nfl_id',np.nan),('combine_position',None),('forty',np.inf)]:
            bad=q.copy();bad.loc[0,col]=value
            with self.assertRaises(ValueError):source_metadata(bad)
        other=q.iloc[:1].copy();other['draft_year']=2025
        with self.assertRaisesRegex(ValueError,'multiple draft classes'):
            source_metadata(pd.concat([q,other]))

    def test_future_nfl_position_and_test_outcomes_cannot_change_forecasts(self):
        q=players();q['nfl_position']='DE'
        tr=q.iloc[:15].copy();te=q.iloc[15:].copy()
        before=model_predict(tr,te,[],10,0)
        tr['nfl_position']='entirely different NFL role';te['nfl_position']=np.arange(len(te))
        te['target']=1-te.target
        after=model_predict(tr,te,[],10,0)
        np.testing.assert_array_equal(before,after)
        np.testing.assert_array_equal(before,model_predict(tr.drop(columns='nfl_position'),te.drop(columns='nfl_position'),[],10,0))

    def test_extractor_never_requires_or_exports_nfl_position(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);q=players(2).drop(columns='target');q['pressure_event']=[0,1]
            q.to_pickle(root/'cohort.pkl')
            tracking=pd.DataFrame([dict(nfl_id=i,draft_year=year,event_id=i*2+year,entity_type='PLAYER',drill_name='PASS_RUSH_DRILL',time='2024-01-01T00:00:00',x=0.,y=0.,s=0.) for i in range(2) for year in (2024,2025)])
            tracking.to_csv(root/'combine_tracking.csv',index=False)
            with patch('run_movement_transfer.ensemble_features',return_value=({'peak_speed':1.},{'scenarios':[{'population':1}]})):
                unit,receipt=extract(root,root/'cohort.pkl',root/'output')
            self.assertIn('combine_position',unit)
            self.assertNotIn('nfl_position',unit)
            self.assertEqual(receipt['source_attempts'],2)
            self.assertTrue(receipt['conventional_source_consistency_checked'])


if __name__=='__main__':unittest.main()
