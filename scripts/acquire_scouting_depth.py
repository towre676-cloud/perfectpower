#!/usr/bin/env python3
"""Fill historical coverage and acquire richer public opportunity tables.

Preserves the original acquisition manifest and cached bytes. Records every
failed URL, including unavailable historical files; no credential is required.
"""
import argparse,concurrent.futures,hashlib,json,urllib.request
from datetime import datetime,timezone
from pathlib import Path


def sources():
    release='https://github.com/sportsdataverse/sportsdataverse-data/releases/download/'
    out=[('nfl_schedule_games.csv','https://raw.githubusercontent.com/nflverse/nfldata/master/data/games.csv')]
    for year in range(2004,2026):
        for tag,stem in [('espn_cfb_player_box','player_box'),('espn_cfb_rosters','cfb_rosters'),('espn_cfb_usage_players','usage_players'),('espn_cfb_usage_tackles','usage_tackles'),('espn_cfb_receiving','cfb_receiving'),('espn_cfb_rushing','cfb_rushing'),('espn_cfb_passing','cfb_passing'),('espn_cfb_team_summaries','cfb_team_summaries')]:
            name=f'{stem}_{year}.parquet';out.append((name,release+tag+'/'+name))
        if year<2014:
            name=f'player_stats_{year}.parquet';out.append((name,'https://raw.githubusercontent.com/sportsdataverse/cfbfastR-data/main/player_stats/parquet/'+name))
    for year in range(2002,2014):
        name=f'cfb_recruits_{year}.parquet';out.append((name,release+'cfb_recruits/'+name))
    for year in range(2007,2026):
        name=f'player_stats_{year}.csv' if year<2025 else f'stats_player_week_{year}.csv'
        tag='player_stats' if year<2025 else 'stats_player'
        out.append((name,'https://github.com/nflverse/nflverse-data/releases/download/'+tag+'/'+name))
    return out


def acquire(cache):
    cache.mkdir(parents=True,exist_ok=True)
    def get(task):
        name,url=task;path=cache/name;record={'name':name,'url':url}
        try:
            reused=path.exists()
            if not reused:
                raw=urllib.request.urlopen(url,timeout=60).read();temporary=path.with_suffix(path.suffix+'.partial');temporary.write_bytes(raw);temporary.replace(path)
            raw=path.read_bytes();record.update(status='acquired',bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest(),cache_reused=reused)
        except Exception as exc:record.update(status='failed',error=str(exc))
        return record
    with concurrent.futures.ThreadPoolExecutor(6) as pool:records=list(pool.map(get,sources()))
    result={'schema':'pp-scouting-depth-acquisition/1','retrieved_utc':datetime.now(timezone.utc).isoformat(),'sources':records,'scope':'Public current-vintage provider archives; not historical snapshots and not complete historical tracking.'}
    (cache/'acquisition_depth.json').write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cache',type=Path,required=True);a=p.parse_args();r=acquire(a.cache)
    print(json.dumps({'acquired':sum(x['status']=='acquired' for x in r['sources']),'failed':[x for x in r['sources'] if x['status']=='failed']}))
