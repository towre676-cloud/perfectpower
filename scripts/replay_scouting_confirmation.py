#!/usr/bin/env python3
"""Replay preserved 2023/2024 rows; never open future confirmation data."""
import hashlib,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'python'))
import pandas as pd
from perfectpower.scouting_confirmation import freeze,score,digest
source=Path(sys.argv[1]);out=Path(sys.argv[2]);expected='77fccd5b270126fa2969ea2983c4e6bd11c12f12b3f0a3dbc9b61446408c56f5'
if hashlib.sha256(source.read_bytes()).hexdigest()!=expected:raise ValueError('preserved source hash mismatch')
q=pd.read_pickle(source)
if set(q.draft_year)!={2023,2024}:raise ValueError('historical cohorts only')
r={'schema':'pp-pressure-historical-replay/1','source_sha256':expected,'development':True,'future_outcomes_opened':False,'cohorts':{}}
for y,g in q.groupby('draft_year'):
 # Unverified vintage: no correction can pass strict gate. Report the original
 # exploratory route separately rather than inventing dated publication proof.
 x=g.copy();x['asof_verified']=False
 p=freeze(x,'development',{},True)
 o=g[['pfr_id','defensive_snaps']].copy();o['pressures']=(g.target*g.defensive_snaps/100).round();o['team_cluster']='unavailable'
 r['cohorts'][str(y)]=score(p,o,'2026-10-28')
 m=g.pos.eq('LB') & g['aggregate'].lt(g['combine']);s=g[m]
 r['cohorts'][str(y)]['original_exploratory_LB_lower']={'n':len(s),'absolute_gain':float(((s.target-s['combine'])**2-(s.target-s['aggregate'])**2).mean())}
r['strict_asof_gate_selected']=0;r['explanation']='Missing publication timestamps block as-of eligibility; no historical pseudo-prospective claim.'
out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(r,indent=2,allow_nan=False)+'\n')
