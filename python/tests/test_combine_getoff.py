"""Synthetic mechanism checks, not evidence of NFL forecasting value."""
import numpy as np
import pandas as pd
import pytest
from perfectpower.combine_getoff import (PHYS,LAUNCH_COLUMNS,CONTEXT_NUM,
    CONTEXT_CAT,Context,GetoffFit,RealBaseline,fit_predict,player_loss,units)


def fixture(players=48,plays=4,signal=False):
    rng=np.random.default_rng(4428);rows=[]
    source=rng.normal(size=(players,2))
    phys=rng.normal(size=(players,len(PHYS))) if not signal else np.zeros((players,len(PHYS)))
    for p in range(players):
        for j in range(plays):
            row={'nfl_id':p,'draft_year':2023+p%2,'game_id':p*100+j,'play_id':j,'combine_position':'DL'}
            row.update(dict(zip(PHYS,phys[p])))
            row.update(dict(zip(LAUNCH_COLUMNS,source[p])))
            row.update({c:float(rng.normal()) for c in CONTEXT_NUM})
            row.update({c:'A' for c in CONTEXT_CAT})
            row['available__PASS_RUSH_DRILL']=1.
            row['player_get_off']=.35+.01*row['snap_depth']+(.025*source[p,0] if signal else .003*rng.normal())
            rows.append(row)
    return pd.DataFrame(rows)


def test_heldout_outcome_and_peer_invariance():
    q=fixture();tr=q[q.nfl_id<36];te=q[q.nfl_id>=36].copy()
    p,a=fit_predict(tr,te,714)
    te['player_get_off']=999.
    for c in PHYS+list(LAUNCH_COLUMNS)+list(CONTEXT_NUM):te.loc[te.nfl_id>36,c]=1e9
    pp,aa=fit_predict(tr,te,714)
    assert a==aa
    for k in p:np.testing.assert_allclose(p[k][te.nfl_id.eq(36)],pp[k][te.nfl_id.eq(36)],rtol=0,atol=1e-14)


def test_real_baseline_has_no_pressure_rate_clip():
    q=fixture();u=units(q,q.player_get_off)
    u['target']=2.
    p=RealBaseline(u.iloc[:36],714).predict(u.iloc[36:])
    np.testing.assert_allclose(p,2.,atol=1e-12)


def test_source_constancy_and_identity_guard():
    q=fixture();bad=q.copy();bad.loc[0,LAUNCH_COLUMNS[0]]+=1
    with pytest.raises(ValueError,match='inconsistent source'):units(bad)
    with pytest.raises(ValueError,match='athlete leakage'):fit_predict(q[q.nfl_id<36],q[q.nfl_id>=35],714)
    with pytest.raises(ValueError,match='duplicate'):units(pd.concat([q,q.iloc[:1]]))


def test_context_excludes_nfl_position_and_labels_at_prediction():
    q=fixture();tr=q[q.nfl_id<36].copy();te=q[q.nfl_id>=36].copy()
    tr['nfl_position']='DE';te['nfl_position']='DT'
    f=Context(tr);p=f.predict(te)
    te['nfl_position']='QB';te['player_get_off']=np.nan
    np.testing.assert_array_equal(p,f.predict(te))


def test_bound_and_exact_zero_fallback():
    q=fixture();q['player_get_off']=.35
    p,a=fit_predict(q[q.nfl_id<36],q[q.nfl_id>=36],714)
    assert a['correction_cap_seconds']==0.
    assert not a['apply_correction']
    np.testing.assert_array_equal(p['selected'],p['conventional'])
    f=GetoffFit(fixture()[lambda x:x.nfl_id<36],714)
    class Huge:
        def predict(self,z):return np.full(len(z),1e6)
    f.correction=Huge();pp=f.predict(fixture()[lambda x:x.nfl_id>=36])
    assert np.max(np.abs(pp['fixed']-pp['conventional']))<=f.cap+1e-14


def test_primary_loss_squares_player_mean_error():
    r=pd.DataFrame({'nfl_id':[1,1,2],'player_get_off':[0.,2.,0.]})
    out=player_loss(r,np.array([1.,1.,1.]))
    assert out.to_dict()=={1:0.,2:1.}


def test_correction_response_nuisance_excludes_its_player_transitively():
    q=fixture(players=36);a=GetoffFit(q,714)
    changed=q.copy();changed.loc[changed.nfl_id.eq(0),'player_get_off']+=100.
    b=GetoffFit(changed,714)
    mask=q.nfl_id.eq(0).to_numpy()
    np.testing.assert_array_equal(a.crossfit_baseline_predictions[mask],b.crossfit_baseline_predictions[mask])

def test_infinite_trusted_source_or_context_is_rejected():
    for col in [PHYS[0],LAUNCH_COLUMNS[0],CONTEXT_NUM[0]]:
        q=fixture();q[col]=np.inf
        with pytest.raises(ValueError,match='infinite numeric'):units(q)
