#!/usr/bin/env python3
"""Outcome-free split-attempt audit of the four declared source coordinates."""
import argparse,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd
from scipy.stats import spearmanr
from perfectpower.combine_compact import COLUMNS

def audit(events):
    # Only source attempts from development classes; never consume NFL labels.
    e=events[events.draft_year.isin([2023,2024])].copy()
    if e.duplicated(['nfl_id','draft_year','event_id']).any():raise ValueError('duplicate attempt')
    r={'schema':'pp-combine-repeatability/1','outcome_free':True,'classes':[2023,2024],'scope':'Deterministic alternating event-ID split within athlete/drill. Repetitions may differ in setup/instruction. Agreement is descriptive, not biological reliability or calibrated phase probability.','features':{}}
    for col in COLUMNS:
        _,drill,f=col.split('__',2);d=e[e.drill_name.eq(drill)].dropna(subset=[f]).sort_values(['nfl_id','event_id']);pairs=[]
        for _,g in d.groupby('nfl_id',sort=True):
            if len(g)>=2:pairs.append((float(g.iloc[::2][f].median()),float(g.iloc[1::2][f].median())))
        x=np.asarray(pairs).reshape(-1,2);n=len(x);corr=float(spearmanr(x[:,0],x[:,1]).statistic) if n>=4 and (np.std(x,axis=0)>0).all() else None
        if corr is not None and not np.isfinite(corr):corr=None
        boot=[];rng=np.random.default_rng(4728)
        if n>=8:
            for _ in range(1000):
                v=x[rng.integers(n,size=n)]
                if (np.std(v,axis=0)>0).all():
                    z=float(spearmanr(v[:,0],v[:,1]).statistic)
                    if np.isfinite(z):boot.append(z)
        r['features'][col]={'attempts':len(d),'players':int(d.nfl_id.nunique()),'repeat_players':n,'split_spearman':corr,'descriptive_player_bootstrap_95':np.quantile(boot,[.025,.975]).tolist() if boot else None,'bootstrap_valid_draws':len(boot),'median_absolute_split_difference':float(np.median(np.abs(x[:,0]-x[:,1]))) if n else None,'units':'Inherited operational feature units; compare within feature only.'}
    return r
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--events',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();r=audit(pd.read_pickle(a.events));r['input_sha256']=hashlib.sha256(a.events.read_bytes()).hexdigest();r['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest();a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2,allow_nan=False)+'\n')
