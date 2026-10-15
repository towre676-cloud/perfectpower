import sys,unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import numpy as np,pandas as pd
from perfectpower.movement_residual import PHYS,splits,choose,fit_predict,repeat_reliability


def fixture():
    rng=np.random.default_rng(904);n=32
    x=pd.DataFrame({c:rng.normal(size=n) for c in PHYS})
    x['nfl_id']=np.arange(n);x['draft_year']=np.repeat([2023,2024],n//2);x['combine_position']='DE';x['target']=np.clip(.1+.01*x.forty,0,1)
    for col in ['peak_speed','order_area_12','phase_sd_0']:
        x['movement__DRILL__'+col]=rng.normal(size=n)
    e=pd.DataFrame({'nfl_id':np.repeat(np.arange(n),2),'drill_name':'DRILL','peak_speed':rng.normal(size=2*n),'order_area_12':rng.normal(size=2*n),'phase_sd_0':rng.normal(size=2*n)})
    return x,e


class ResidualTests(unittest.TestCase):
    def test_bootstrap_duplicates_stay_together(self):
        x,_=fixture();x=pd.concat([x,x.iloc[:8]],ignore_index=True)
        seen=[]
        for i,j in splits(x,4):
            self.assertFalse(set(x.iloc[i].nfl_id)&set(x.iloc[j].nfl_id));seen.extend(j)
        self.assertEqual(sorted(seen),list(range(len(x))))
    def test_zero_selected_on_harmful_correction(self):
        y=np.arange(10.)/10;z=('zero',0.,0.)
        pick,a=choose({z:y,('ordered',1.,1.):y+.1},y)
        self.assertEqual(pick,z)
    def test_one_se_rule_preserves_exact_baseline(self):
        y=np.zeros(4);z=('zero',0.,0.);c=('ordered',1.,1.)
        pick,_=choose({z:np.array([1.,0,0,0]),c:np.array([0,0,0,.9])},y)
        self.assertEqual(pick,z)
    def test_source_reliability_is_train_only(self):
        x,e=fixture();cols=['movement__DRILL__peak_speed'];ids=set(range(20))
        a,_=repeat_reliability(e,ids,cols);e.loc[~e.nfl_id.isin(ids),'peak_speed']=1e12
        b,_=repeat_reliability(e,ids,cols);np.testing.assert_array_equal(a,b)
        unique=e.drop_duplicates('nfl_id');w,_=repeat_reliability(unique,ids,cols);np.testing.assert_array_equal(w,[0])
    def test_whole_estimator_ignores_held_labels_and_peers(self):
        x,e=fixture();tr=x.iloc[:24];te=x.iloc[24:].copy();a,aa=fit_predict(tr,te,e)
        te['target']=1-te.target;te.iloc[1:,te.columns.get_loc('forty')]=1e12
        for c in te:
            if c.startswith('movement__'):te.iloc[1:,te.columns.get_loc(c)]=1e12
        b,bb=fit_predict(tr,te,e)
        self.assertEqual(aa,bb)
        for key in a:self.assertEqual(a[key][0],b[key][0])
    def test_overlap_rejected(self):
        x,e=fixture()
        with self.assertRaisesRegex(ValueError,'leakage'):fit_predict(x.iloc[:24],x.iloc[23:],e)
    def test_known_incremental_signal_is_recovered(self):
        x,e=fixture();x=pd.concat([x]*5,ignore_index=True)
        rng=np.random.default_rng(188);x['nfl_id']=np.arange(len(x))
        x['movement__DRILL__order_area_12']=rng.normal(size=len(x))
        x['target']=np.clip(.3+.06*x['movement__DRILL__order_area_12'],0,1)
        p,a=fit_predict(x.iloc[:120],x.iloc[120:],e)
        y=x.iloc[120:].target.to_numpy()
        self.assertLess(np.mean((y-p['selected'])**2),.25*np.mean((y-p['conventional'])**2))
        self.assertNotEqual(a['selection']['selected']['config'][0],'zero')

if __name__=='__main__':unittest.main()
