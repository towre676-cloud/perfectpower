#!/usr/bin/env python3
"""Extract two 0.5-second source-launch coordinates and retain exact rush roster."""
import argparse,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd
from perfectpower.combine_getoff import LAUNCH_COLUMNS,CONTEXT_NUM,CONTEXT_CAT,KEYS
from perfectpower.movement_residual import PHYS

def launch_features(time,xy,speed):
    t=np.asarray(time,float);p=np.asarray(xy,float);s=np.asarray(speed,float)
    if len(t)<6 or p.shape!=(len(t),2) or s.shape!=t.shape or not np.isfinite(np.c_[t,p,s]).all():raise ValueError('short_or_nonfinite')
    if not np.allclose(np.diff(t),.1,atol=.015,rtol=0) or (s<0).any():raise ValueError('irregular_or_negative_speed')
    onset=next((i for i in range(len(s)-2) if np.all(s[i:i+3]>1.)),None)
    if onset is None or t[-1]<t[onset]+.5-1e-9:raise ValueError('no_complete_launch_window')
    # Fixed sustained motion threshold, not an official start cue or reaction time.
    end=t[onset]+.5
    endpoint=np.array([np.interp(end,t,p[:,j]) for j in range(2)])
    return {LAUNCH_COLUMNS[0]:float(np.interp(end,t,s)-s[onset]),LAUNCH_COLUMNS[1]:float(np.linalg.norm(endpoint-p[onset]))}

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def prepare(data,cohort,players,out):
    rows=pd.read_pickle(cohort);unit=pd.read_pickle(players)
    if len(rows)!=14665 or rows.nfl_id.nunique()!=74 or unit.groupby('draft_year').size().to_dict()!={2023:23,2024:22,2025:29}:raise ValueError('fixed historical roster mismatch')
    if rows.duplicated(list(KEYS)).any() or unit.nfl_id.duplicated().any():raise ValueError('duplicate identities')
    if set(zip(rows.nfl_id,rows.draft_year))!=set(zip(unit.nfl_id,unit.draft_year)):raise ValueError('cohort/source identity mismatch')
    tracking=data/'combine_tracking.csv';expected=json.loads((ROOT/'research/kaggle_combine/upstream/manifest.json').read_text())['official_source_sha256']['combine_tracking.csv']
    if sha(tracking)!=expected:raise ValueError('source tracking changed')
    tr=pd.read_csv(tracking);tr=tr[tr.entity_type.eq('PLAYER')&tr.drill_name.eq('PASS_RUSH_DRILL')].merge(unit[['nfl_id','draft_year']],on=['nfl_id','draft_year'],validate='many_to_one');attempts=[];reject={}
    for key,g in tr.groupby(['nfl_id','draft_year','event_id'],sort=True):
        g=g.sort_values('time');ts=pd.to_datetime(g.time);seconds=(ts-ts.iloc[0]).dt.total_seconds().to_numpy()
        try:z=launch_features(seconds,g[['x','y']].to_numpy(),g.s.to_numpy())
        except ValueError as e:reject[str(e)]=reject.get(str(e),0)+1;continue
        attempts.append(dict(nfl_id=key[0],draft_year=key[1],event_id=key[2],**z))
    if not attempts:raise ValueError('no valid source attempts')
    events=pd.DataFrame(attempts);med=events.groupby(['nfl_id','draft_year'])[list(LAUNCH_COLUMNS)].median().reset_index()
    keep=['nfl_id','draft_year','combine_position']+PHYS+sorted(c for c in unit if c.startswith('available__'))
    source=unit[keep].merge(med,on=['nfl_id','draft_year'],how='left',validate='one_to_one');source['available__LAUNCH_0p5']=source[list(LAUNCH_COLUMNS)].notna().all(axis=1).astype(float)
    context=list(KEYS)+['draft_year','player_get_off']+list(CONTEXT_NUM)+list(CONTEXT_CAT)
    result=rows[context].merge(source,on=['nfl_id','draft_year'],validate='many_to_one')
    out.mkdir(parents=True,exist_ok=True);result.to_pickle(out/'rushes.pkl');events.to_pickle(out/'launch_events.pkl')
    r={'schema':'pp-combine-getoff-extraction/1','source_tracking_sha256':expected,'cohort_sha256':sha(cohort),'source_players_sha256':sha(players),'source_sha256':sha(Path(__file__)),'rushes':len(result),'players':result.nfl_id.nunique(),'by_class':{str(k):int(v) for k,v in result.groupby('draft_year').nfl_id.nunique().items()},'source_attempts':len(events),'rejections':reject,'players_with_launch':int(source.available__LAUNCH_0p5.sum()),'feature_columns':list(LAUNCH_COLUMNS),'predictor_scope':'Combine-only launch; observed NFL context supplied separately for conditional get-off predictions. No pressure outcomes, team IDs, eventual NFL position or post-play metrics retained.','onset':'First three consecutive speed samples>1yd/s, then endpoint speed gain and Euclidean displacement at+0.5s; 10Hz near-contiguous frames and actual-time interpolation to exactly+0.5s, no official cue/reaction claim.'}
    (out/'extraction.json').write_text(json.dumps(r,indent=2)+'\n');return r
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['data','cohort','players','out']:p.add_argument('--'+key,type=Path,required=True)
    a=p.parse_args()
    if a.out.resolve()==ROOT or ROOT in a.out.resolve().parents:p.error('private output must stay outside checkout')
    print(json.dumps(prepare(**vars(a))))
