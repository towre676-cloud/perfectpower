#!/usr/bin/env python3
"""Extend the preserved population without changing its outcomes or identities."""
import argparse,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd
from perfectpower.scouting_metrics import college_box_features,college_event_features,attach_college
from perfectpower.scouting_depth import aggregate_usage,attach_usage,resolve_college_ids,extend_receiving_population


def prepare(cache,previous,out,first_year=2007):
    rows=pd.read_pickle(previous/'prospects.pkl');history=pd.read_pickle(previous/'college_history.pkl');older=[];audit=[]
    if first_year==2007:rows=extend_receiving_population(rows,pd.read_csv(cache/'combine.csv'),pd.read_csv(cache/'draft_picks.csv'),pd.read_csv(cache/'players.csv',low_memory=False))
    elif first_year!=2013:raise ValueError('supported population floors: 2007, 2013')
    rosters=pd.concat([pd.read_parquet(cache/f'cfb_rosters_{year}.parquet')[['season','athlete_id','athlete_display_name','full_name','date_of_birth']] for year in range(2004,2024) if (cache/f'cfb_rosters_{year}.parquet').exists()],ignore_index=True)
    rows,identity_audit=resolve_college_ids(rows,rosters)
    for year in range(2004,2014):
        bpath=cache/f'player_box_{year}.parquet';epath=cache/f'player_stats_{year}.parquet'
        if not bpath.exists():continue
        box=pd.read_parquet(bpath);b=college_box_features(box)
        if epath.exists():b=b.merge(college_event_features(pd.read_parquet(epath)),on=['season','athlete_id'],how='outer',validate='one_to_one')
        older.append(b);audit.append({'year':year,'players':len(b),'box_rows':len(box),'event_available':epath.exists()})
    hist=pd.concat(older+[history],ignore_index=True)
    discard=[c for c in rows if c.startswith(('college_raw__','_college_','metric__college','metric__rush_','metric__receiving_','metric__passing_','metric__trend_'))]
    rows=attach_college(rows.drop(columns=discard),hist)
    links={}
    for kind,stem in [('offense','usage_players'),('defense','usage_tackles')]:
        frames=[aggregate_usage(pd.read_parquet(cache/f'{stem}_{year}.parquet'),kind) for year in range(2004,2026) if (cache/f'{stem}_{year}.parquet').exists()]
        rows,links[kind]=attach_usage(rows,pd.concat(frames,ignore_index=True),kind)
    # Exact GSIS/PFR crosswalk. A missing stat record is never an efficiency zero.
    players=pd.read_csv(cache/'players.csv',low_memory=False);cross=players.dropna(subset=['gsis_id','pfr_id'])[['gsis_id','pfr_id']]
    if cross.gsis_id.duplicated().any() or cross.pfr_id.duplicated().any():raise ValueError('ambiguous NFL statistics crosswalk')
    nfl=pd.concat([pd.read_csv(cache/(f'player_stats_{year}.csv' if year<2025 else f'stats_player_week_{year}.csv'),low_memory=False) for year in range(2007,2026)],ignore_index=True)
    nfl=nfl[nfl.season_type.eq('REG')].merge(cross,left_on='player_id',right_on='gsis_id',how='inner',validate='many_to_one')
    ambiguous_nfl=set(nfl.loc[nfl.duplicated(['season','week','player_id'],keep=False),'pfr_id'])
    # Older sources split one QB's ordinary and two-point passing rows. Reject
    # every ambiguous player's efficiency outcome instead of guessing totals.
    nfl=nfl[~nfl.pfr_id.isin(ambiguous_nfl)].copy()
    totals=nfl.groupby(['season','pfr_id'])[['targets','receiving_yards']].sum(min_count=1)
    target=[];support=[]
    for row in rows.itertuples():
        keys=[(year,row.pfr_id) for year in (row.draft_year,row.draft_year+1) if (year,row.pfr_id) in totals.index]
        obs=totals.loc[keys].sum() if keys else pd.Series({'targets':np.nan,'receiving_yards':np.nan})
        n=float(obs.targets);support.append(n);target.append(float(obs.receiving_yards/n) if row.pos in ('WR','TE') and n>=30 else np.nan)
    rows['receiving_efficiency']=target;rows['nfl_receiving_targets']=support
    out.mkdir(parents=True,exist_ok=True);rows.to_pickle(out/'prospects.pkl')
    return {'schema':'pp-scouting-depth-population/1','players':len(rows),'older_college':audit,'college_identity_bridge':identity_audit,'college_name_verified_players':int(rows[[f'_college_name_verified__lag{k}' for k in (1,2,3)]].any(axis=1).sum()),'usage_name_verified_links':links,'receiving_eligible':int(rows.receiving_efficiency.notna().sum()),'previous_input_sha256':hashlib.sha256((previous/'prospects.pkl').read_bytes()).hexdigest(),'derived_input_sha256':hashlib.sha256((out/'prospects.pkl').read_bytes()).hexdigest(),'original_primary_and_pressure_outcomes_unchanged':True}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cache',type=Path,required=True);p.add_argument('--previous',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--aggregate',type=Path,required=True);p.add_argument('--first-year',type=int,choices=[2007,2013],default=2007);a=p.parse_args()
    if ROOT==a.out.resolve() or ROOT in a.out.resolve().parents:p.error('player cache must be outside checkout')
    r=prepare(a.cache,a.previous,a.out,a.first_year);a.aggregate.parent.mkdir(parents=True,exist_ok=True);a.aggregate.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
