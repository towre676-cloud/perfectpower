#!/usr/bin/env python3
"""Audit all downloaded public tables, including unused roster/recruit sources."""
import argparse,hashlib,json
from pathlib import Path
import pandas as pd


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cache',type=Path,required=True);p.add_argument('--aggregate',type=Path,required=True);a=p.parse_args();manifest=json.loads((a.cache/'acquisition.json').read_text());tables=[];roster_ids=set();college_event_rows=0;college_box_rows=0
    for src in manifest['sources']:
        if src['status']!='acquired':continue
        f=a.cache/src['name'];raw=f.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=src['sha256']:raise ValueError('changed cache: '+f.name)
        x=pd.read_parquet(f) if f.suffix=='.parquet' else pd.read_csv(f,low_memory=False)
        row={'name':f.name,'rows':len(x),'columns':len(x.columns),'sha256':src['sha256'],'provider':src['provider']}
        if 'cfb_rosters' in f.name:
            roster_ids.update(pd.to_numeric(x.athlete_id,errors='coerce').dropna().astype(int));row['warning']='Historical roster records also contain current-looking age, draft and status fields. None used as prospect features. Stable IDs/names only are suitable for audited joining.'
        if 'cfb_recruits' in f.name:row['warning']='Recruit IDs use the 247-style identifier, while roster cfbd_recruit_ids use another namespace. No numeric-only or fuzzy-name join performed.'
        if f.name.startswith('player_stats_'):college_event_rows+=len(x)
        if f.name.startswith('player_box_'):college_box_rows+=len(x)
        tables.append(row)
    result={'schema':'pp-scouting-source-audit/1','source_archives':len(tables),'empty_tables':[t['name'] for t in tables if t['rows']==0],'college_event_rows':college_event_rows,'college_box_rows':college_box_rows,'distinct_college_roster_ids':len(roster_ids),'tables':tables,'evaluated_vs_acquired':'The fixed empirical bank uses the original 42 archives. Twenty-four roster/recruiting archives were added for source coverage/identity work, not retroactively counted as model inputs or successful validation.'}
    a.aggregate.parent.mkdir(parents=True,exist_ok=True);a.aggregate.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='tables'}))
if __name__=='__main__':main()
