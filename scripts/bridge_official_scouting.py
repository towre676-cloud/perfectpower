#!/usr/bin/env python3
"""Attach custom source metrics to all authorized BDB prospect rows, privately.

This is coverage/feature integration, not another validation or a PerfectJet
model overwrite. No NFL outcomes enter this bridge.
"""
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd
from perfectpower.scouting_metrics import physics_features,attach_college,name_key,exact_unique


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--official-data',type=Path,required=True);p.add_argument('--public-cache',type=Path,required=True);p.add_argument('--college-history',type=Path,required=True);p.add_argument('--private-out',type=Path,required=True);p.add_argument('--aggregate',type=Path,required=True);a=p.parse_args()
    if ROOT==a.private_out.resolve() or ROOT in a.private_out.resolve().parents:p.error('private output must be outside repository')
    c=pd.read_csv(a.official_data/'combine_results.csv');p=pd.read_csv(a.official_data/'players.csv');cross=pd.read_csv(a.public_cache/'players.csv',low_memory=False)
    cross=exact_unique(cross,['nfl_id'],'NFL numeric crosswalk')[['nfl_id','pfr_id','espn_id','display_name']].rename(columns={'display_name':'cross_display_name'})
    unit=c.merge(p[['nfl_id','display_name','birth_date']],on='nfl_id',validate='one_to_one').merge(cross,on='nfl_id',how='left',validate='one_to_one')
    aliases={'height_inches':'combine_height','wt':'combine_weight','bench':'bench_reps','cone':'three_cone','shuttle':'short_shuttle'}
    for new,old in aliases.items():unit[new]=unit[old]
    unit['_join_names']=[tuple(sorted({name_key(a),name_key(b)})) for a,b in zip(unit.display_name,unit.cross_display_name)]
    unit=pd.concat([unit,physics_features(unit)],axis=1);unit['metric__first_ten_mean_speed']=9.144/unit.ten_yd_split;unit['metric__later_thirty_mean_speed']=27.432/(unit.forty-unit.ten_yd_split)
    unit['metric__late_early_speed_ratio']=unit['metric__later_thirty_mean_speed']/unit['metric__first_ten_mean_speed']
    unit=attach_college(unit,pd.read_pickle(a.college_history));unit.to_pickle(a.private_out)
    raw=[c for c in unit if c.startswith('college_raw__')];metric=[c for c in unit if c.startswith('metric__')]
    receipt={'schema':'pp-official-scouting-bridge/1','source_players':len(unit),'exact_public_id_links':int(unit.pfr_id.notna().sum()),'college_name_verified':int(unit[[f'_college_name_verified__lag{k}' for k in (1,2,3)]].any(axis=1).sum()),'custom_metric_columns':len(metric),'by_class':{str(y):len(g) for y,g in unit.groupby('draft_year')},'outcome_evaluation_performed':False,'NFL_outcomes_used_as_features':False,'PerfectJet_files_modified':False,'scope':'Feature-only expansion of the authorized 510-player BDB population. This does not turn the historical Combine pool into full trajectories or establish scouting accuracy.'}
    a.aggregate.parent.mkdir(parents=True,exist_ok=True);a.aggregate.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
if __name__=='__main__':main()
