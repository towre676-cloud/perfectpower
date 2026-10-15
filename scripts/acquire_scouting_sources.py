#!/usr/bin/env python3
"""Acquire public scouting sources to an explicit cache; never request Kaggle login.

Existing cache bytes are reused. Manifest records byte hashes and failures,
including empty-but-readable tables. Raw data stays outside the source checkout.
"""
import argparse,concurrent.futures,hashlib,json,urllib.request
from datetime import datetime,timezone
from pathlib import Path


def sources():
    base='https://github.com/nflverse/nflverse-data/releases/download/'
    tasks=[('combine.csv',base+'combine/combine.csv','nflverse'),('draft_picks.csv',base+'draft_picks/draft_picks.csv','nflverse'),('players.csv',base+'players/players.csv','nflverse'),('advstats_season_def.csv',base+'pfr_advstats/advstats_season_def.csv','nflverse')]
    for y in range(2012,2026):tasks.append((f'snap_counts_{y}.csv',base+f'snap_counts/snap_counts_{y}.csv','nflverse'))
    for y in range(2014,2026):
        tasks.append((f'player_stats_{y}.parquet',f'https://raw.githubusercontent.com/sportsdataverse/cfbfastR-data/main/player_stats/parquet/player_stats_{y}.parquet','sportsdataverse_event_participants'))
        tasks.append((f'player_box_{y}.parquet',f'https://github.com/sportsdataverse/sportsdataverse-data/releases/download/espn_cfb_player_box/player_box_{y}.parquet','sportsdataverse_box_scores'))
        tasks.append((f'cfb_rosters_{y}.parquet',f'https://github.com/sportsdataverse/sportsdataverse-data/releases/download/espn_cfb_rosters/cfb_rosters_{y}.parquet','sportsdataverse_rosters'))
        tasks.append((f'cfb_recruits_{y}.parquet',f'https://github.com/sportsdataverse/sportsdataverse-data/releases/download/cfb_recruits/cfb_recruits_{y}.parquet','sportsdataverse_recruiting'))
    return tasks


def acquire(dest):
    dest.mkdir(parents=True,exist_ok=True)
    def get(task):
        name,url,provider=task;p=dest/name
        try:
            cached=p.exists()
            if not cached:
                raw=urllib.request.urlopen(url,timeout=60).read();tmp=p.with_suffix(p.suffix+'.partial');tmp.write_bytes(raw);tmp.replace(p)
            raw=p.read_bytes()
            return {'name':name,'url':url,'provider':provider,'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'cache_reused':cached,'status':'acquired'}
        except Exception as e:return {'name':name,'url':url,'provider':provider,'status':'failed','error':str(e)}
    with concurrent.futures.ThreadPoolExecutor(6) as pool:records=list(pool.map(get,sources()))
    result={'schema':'pp-scouting-source-acquisition/1','retrieved_utc':datetime.now(timezone.utc).isoformat(),'sources':records,'raw_scope':'Public provider datasets, not restricted BDB rows. Source publication/terms remain those of upstream providers. Cached bytes may be revised relative to original game dates; this is not a historical vintage database.'}
    (dest/'acquisition.json').write_text(json.dumps(result,indent=2)+'\n');return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cache',type=Path,required=True);a=p.parse_args();r=acquire(a.cache);print(json.dumps({'acquired':sum(s['status']=='acquired' for s in r['sources']),'failed':[s for s in r['sources'] if s['status']!='acquired']}))
if __name__=='__main__':main()
