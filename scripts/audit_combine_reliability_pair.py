#!/usr/bin/env python3
"""Exploratory paired rank-stability audit, source attempts only; no NFL labels."""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
import pandas as pd
from scipy.stats import spearmanr

COLUMNS=('speed_gain','recovery_accel')


def audit(events, draws=4000, seed=20261104):
    e=events.loc[events.draft_year.isin([2023,2024]) & events.drill_name.eq('PASS_RUSH_DRILL'),['nfl_id','draft_year','event_id',*COLUMNS]].copy()
    if e.duplicated(['nfl_id','draft_year','event_id']).any():raise ValueError('duplicate attempt')
    # Complete attempts shared by both metrics; do not compare different panels.
    e=e.replace([np.inf,-np.inf],np.nan).dropna(subset=list(COLUMNS))
    pairs=[]
    for _,g in e.sort_values(['nfl_id','event_id']).groupby('nfl_id',sort=True):
        if len(g)>=2:pairs.append(np.stack([g.iloc[::2][list(COLUMNS)].median().to_numpy(),g.iloc[1::2][list(COLUMNS)].median().to_numpy()]))
    x=np.asarray(pairs)
    if len(x)<8:raise ValueError('at least eight repeated players required')
    def correlations(v):
        return np.array([spearmanr(v[:,0,j],v[:,1,j]).statistic for j in range(2)])
    point=correlations(x);rng=np.random.default_rng(seed);boot=[]
    for _ in range(draws):
        c=correlations(x[rng.integers(len(x),size=len(x))])
        if np.isfinite(c).all():boot.append(c[0]-c[1])
    return {'schema':'pp-combine-reliability-pair/1','status':'exploratory source-only diagnostic after marginal correlations were known','outcome_free':True,'classes':[2023,2024],'players':len(x),'complete_shared_attempts':len(e),'speed_gain_rho':float(point[0]),'recovery_accel_rho':float(point[1]),'rho_difference':float(point[0]-point[1]),'paired_player_bootstrap_95':np.quantile(boot,[.025,.975]).tolist(),'draws':draws,'valid_draws':len(boot),'seed':seed,'scope':'Resample common players jointly across both metrics and attempt halves. Pointwise percentile diagnostic, no multiplicity or researcher-selection adjustment. Varying attempt conditions; not a controlled test-retest experiment. No NFL responses consumed; no predictive model fitted or selected.'}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--events',required=True,type=Path);p.add_argument('--expected-sha256',required=True);p.add_argument('--out',required=True,type=Path);a=p.parse_args()
    digest=hashlib.sha256(a.events.read_bytes()).hexdigest()
    if digest!=a.expected_sha256:raise ValueError('Saved source-attempt bytes do not match historical receipt')
    r=audit(pd.read_pickle(a.events));r['input_sha256']=digest;r['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
