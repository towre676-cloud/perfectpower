"""Synthetic estimator checks, not empirical NFL validation."""
import unittest

import numpy as np
import pandas as pd

from perfectpower.combine_compact import COLUMNS,CompactFit,fit_predict
from perfectpower.movement_residual import PHYS


def fixture(n=48, signal=False):
    rng=np.random.default_rng(8813)
    q=pd.DataFrame({c:np.zeros(n) if signal else rng.normal(size=n) for c in PHYS})
    q['nfl_id']=np.arange(n);q['draft_year']=np.where(q.nfl_id%2,2023,2024)
    q['combine_position']='DE'
    for c in COLUMNS:q[c]=rng.normal(size=n)
    q['available__PASS_RUSH_DRILL']=1.
    if signal:
        for c in COLUMNS[1:]:q[c]=0.
        q['target']=.2+.01*np.clip(q[COLUMNS[0]],-2,2)
    else:q['target']=np.clip(.15+.01*q.forty,0,1)
    return q


class CompactTests(unittest.TestCase):
    def test_heldout_labels_and_peers_cannot_change_forecast(self):
        q=fixture();tr=q.iloc[:36];te=q.iloc[36:].copy()
        p,a=fit_predict(tr,te,714)
        te['target']=1-te.target
        for c in list(PHYS)+list(COLUMNS):te.iloc[1:,te.columns.get_loc(c)]=1e12
        pp,aa=fit_predict(tr,te,714)
        # The maximum over held-out corrections may change with peer features.
        a.pop('maximum_absolute_fixed_change');aa.pop('maximum_absolute_fixed_change')
        self.assertEqual(a,aa)
        for key in p:self.assertEqual(p[key][0],pp[key][0])

    def test_unobserved_source_coordinate_has_no_learned_effect(self):
        q=fixture();q[COLUMNS[2]]=np.nan
        fit=CompactFit(q.iloc[:36],714);te=q.iloc[36:].copy()
        before=fit.predict(te)
        te[COLUMNS[2]]=1e12
        after=fit.predict(te)
        for a,b in zip(before,after):np.testing.assert_array_equal(a,b)

    def test_fixed_change_is_capped(self):
        q=fixture();fit=CompactFit(q.iloc[:36],714);te=q.iloc[36:]
        class HugeCorrection:
            def predict(self,x):return np.full(len(x),1e6)
        fit.correction=HugeCorrection()
        base,fixed=fit.predict(te)
        self.assertTrue(np.all(np.abs(fixed-base)<=.0200000000000001))
        np.testing.assert_allclose(fixed-base,.02,atol=1e-15,rtol=0)

    def test_exact_zero_fallback(self):
        q=fixture();q['target']=0.
        p,a=fit_predict(q.iloc[:36],q.iloc[36:],714)
        self.assertFalse(a['apply_correction'])
        np.testing.assert_array_equal(p['selected'],p['conventional'])
        self.assertEqual(a['inner_gain'],0.)

    def test_known_small_incremental_signal_is_recovered(self):
        q=fixture(100,signal=True)
        p,a=fit_predict(q.iloc[:76],q.iloc[76:],714);y=q.iloc[76:].target.to_numpy()
        self.assertTrue(a['apply_correction'])
        self.assertLess(np.mean((y-p['selected'])**2),.5*np.mean((y-p['conventional'])**2))
        self.assertLessEqual(a['maximum_absolute_fixed_change'],.0200000000000001)

    def test_identity_overlap_rejected(self):
        q=fixture()
        with self.assertRaisesRegex(ValueError,'athlete leakage'):
            fit_predict(q.iloc[:36],q.iloc[35:],714)


if __name__=='__main__':unittest.main()
