"""Outcome-blind routing and immutable prediction/paired scoring packets.

No acquisition occurs here. Future outcomes are accepted only after maturity.
"""
import hashlib
import json
from datetime import date
import numpy as np
import pandas as pd

MODELS=('combine','role_mean','aggregate','no_correction','candidate')
FEATURES=('pfr_id','draft_year','pos','identity_status','asof_verified','combine','role_mean','aggregate')

def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()

def freeze(rows, protocol_sha, lineage, development=False):
    # An allowlist ensures target, exposure and NFL role never enter routing.
    q=rows[list(FEATURES)].copy().sort_values('pfr_id').reset_index(drop=True)
    if q.empty or q.pfr_id.isna().any() or q.pfr_id.duplicated().any():raise ValueError('nonempty unique identities required')
    if not q.pos.isin(['LB','DE','DT','EDGE','DL']).all():raise ValueError('defensive population required')
    if not np.isfinite(q[['combine','role_mean','aggregate']].to_numpy(float)).all():raise ValueError('finite forecasts required')
    if not q[['combine','role_mean','aggregate']].apply(lambda c:c.between(0,100)).all().all():raise ValueError('rate bounds')
    if not q.asof_verified.map(lambda x:isinstance(x,(bool,np.bool_))).all():raise ValueError('explicit Boolean availability required')
    if not development:
        if set(q.draft_year)!={2025}:raise ValueError('confirmation class must be 2025')
        if lineage['latest_training_class']>2023:raise ValueError('immature training labels')
        for key in ('feature_manifest_sha256','model_artifact_sha256','training_manifest_sha256'):
            if len(lineage.get(key,''))!=64:raise ValueError('missing lineage '+key)
    q['selected']=q.pos.eq('LB') & q.identity_status.eq('verified_name_birth') & q.asof_verified & q['aggregate'].lt(q['combine'])
    q['no_correction']=q['combine'];q['candidate']=np.where(q.selected,q['aggregate'],q['combine'])
    payload={'schema':'pp-pressure-freeze/1','development':development,'protocol_sha256':protocol_sha,'lineage':lineage,'rows':q.to_dict('records')}
    return {'payload':payload,'sha256':digest(payload)}

def interval(values,groups,alpha,seed=42871,draws=10000):
    # Cluster resampling uses every player in each sampled team block.
    unique=sorted(set(groups));rng=np.random.default_rng(seed)
    if len(unique)<8:return None
    blocks=[values[np.asarray(groups)==g] for g in unique]
    samples=[np.concatenate([blocks[i] for i in rng.integers(len(blocks),size=len(blocks))]).mean() for _ in range(draws)]
    return np.quantile(samples,[alpha/2,1-alpha/2]).tolist()

def score(packet,outcomes,as_of,complete=False):
    p=packet['payload']
    if digest(p)!=packet['sha256']:raise ValueError('freeze changed')
    if not p['development'] and (date.fromisoformat(as_of)<date(2027,3,1) or not complete):raise ValueError('full 2025/2026 REG window and source completeness required')
    q=pd.DataFrame(p['rows']);o=outcomes.copy()
    if o.pfr_id.duplicated().any() or set(o.pfr_id)!=set(q.pfr_id):raise ValueError('exact frozen identity coverage required')
    if not o[['pressures','defensive_snaps']].apply(lambda c:np.isfinite(c)&c.ge(0)&c.eq(np.floor(c))).all().all():raise ValueError('nonnegative integer counts required')
    if o.team_cluster.isna().any():raise ValueError('team cluster required')
    if (o.pressures>o.defensive_snaps).any():raise ValueError('invalid pressure counts')
    q=q.merge(o[['pfr_id','pressures','defensive_snaps','team_cluster']],validate='one_to_one');q['target']=100*q.pressures/q.defensive_snaps.replace(0,np.nan)
    report={'schema':'pp-pressure-score/1','development':p['development'],'freeze_sha256':packet['sha256'],'outcome_sha256':digest(o.sort_values('pfr_id').to_dict('records')),'zero_exposure':int(q.target.isna().sum()),'groups':{}}
    # 2 prespecified populations x 4 comparisons = 8 simultaneous intervals.
    for name,mask in [('selected_LB',q.selected),('all_defense',pd.Series(True,index=q.index))]:
        g=q[mask & q.target.notna()];r={'n':len(g),'frozen_n':int(mask.sum()),'comparisons':{}}
        for baseline in MODELS[:-1]:
            a=(g.target-g.candidate).pow(2).to_numpy();b=(g.target-g[baseline]).pow(2).to_numpy();gain=b-a
            r['comparisons'][baseline]={'candidate_mse':float(a.mean()) if len(g) else None,'baseline_mse':float(b.mean()) if len(g) else None,'absolute_gain':float(gain.mean()) if len(g) else None,'relative_gain':float(gain.mean()/b.mean()) if len(g) and b.mean()>0 else None,'simultaneous_95_team_interval':interval(gain,g.team_cluster.to_numpy(),.05/8) if len(g) else None}
        report['groups'][name]=r
    s=report['groups']['selected_LB'];a=report['groups']['all_defense']
    report['success']=bool(not p['development'] and s['n']>=20 and all(s['comparisons'][b]['simultaneous_95_team_interval'] is not None and s['comparisons'][b]['simultaneous_95_team_interval'][0]>0 for b in ('combine','role_mean')) and a['comparisons']['combine']['simultaneous_95_team_interval'] is not None and a['comparisons']['combine']['simultaneous_95_team_interval'][0]>=0)
    report['models_promoted']=False
    return report
