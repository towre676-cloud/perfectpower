#!/usr/bin/env python3
"""Audit acquisition bytes, observed denominators and NFL season completeness."""
import argparse,hashlib,json
from pathlib import Path
import numpy as np,pandas as pd


def audit(cache,original,extended):
    catalog={};failures=[]
    for manifest in ('acquisition.json','acquisition_depth.json'):
        for source in json.loads((cache/manifest).read_text())['sources']:
            if source['status']!='acquired':failures.append(source);continue
            path=cache/source['name'];digest=hashlib.sha256(path.read_bytes()).hexdigest()
            if digest!=source['sha256'] or path.stat().st_size!=source['bytes']:raise ValueError('source bytes changed: '+source['name'])
            if source['name'] in catalog and catalog[source['name']]['sha256']!=digest:raise ValueError('manifest hash conflict')
            catalog[source['name']]=source
    coverage={};schedule=pd.read_csv(cache/'nfl_schedule_games.csv',low_memory=False)
    for year in range(2007,2026):
        name=f'player_stats_{year}.csv' if year<2025 else f'stats_player_week_{year}.csv'
        x=pd.read_csv(cache/name,low_memory=False);x=x[x.season_type.eq('REG')].copy();team='recent_team' if 'recent_team' in x else 'team'
        duplicated=x.duplicated(['season','week','player_id'],keep=False)
        games=x[['week',team,'opponent_team']].drop_duplicates();games['_pair']=[tuple(sorted([a,b])) for a,b in zip(games[team],games.opponent_team)]
        groups=games.groupby(['week','_pair'])[team].nunique();observed=set(groups[groups.eq(2)].index)
        official=schedule[schedule.season.eq(year) & schedule.game_type.eq('REG') & schedule.home_score.notna()];aliases={'STL':'LA','SD':'LAC','OAK':'LV'}
        actual={(int(r.week),tuple(sorted([aliases.get(r.home_team,r.home_team),aliases.get(r.away_team,r.away_team)]))) for r in official.itertuples()}
        n=len(observed);expected=271 if year==2022 else 272 if year>=2021 else 256
        if n!=expected or x[team].nunique()!=32 or observed!=actual:raise ValueError('incomplete NFL performance source '+str(year))
        coverage[str(year)]={'observed_reciprocal_games':n,'expected_games':expected,'exact_schedule_match':True,'teams':32,'weekly_player_rows':len(x),'unilateral_source_team_opponent_pairs':int(groups.eq(1).sum()),'context_scope':'Legacy source has unilateral team/opponent anomalies. Never used as predictors or denominators; reciprocal pair sets match the full schedule. Player receiving totals use source GSIS and season only.','ambiguous_weekly_rows':int(duplicated.sum()),'ambiguous_players_quarantined_from_efficiency':int(x.loc[duplicated,'player_id'].nunique())}
    u=pd.read_pickle(original);v=pd.read_pickle(extended);common=v[v.pfr_id.isin(u.pfr_id)].set_index('pfr_id').loc[u.pfr_id]
    for col in ('target','pressure_target','two_season_snaps'):
        np.testing.assert_equal(u[col].to_numpy(),common[col].to_numpy())
    old=v[v.draft_year.lt(2013)]
    if old[['target','pressure_target','two_season_snaps']].notna().any().any():raise ValueError('invented older snap or pressure outcomes')
    constraints=[]
    for path in sorted(cache.glob('usage_players_*.parquet')):
        x=pd.read_parquet(path);bad=(x.receptions.gt(x.targets)|x.fd_or_td.gt(x.opportunities)|x.explosive_plays.gt(x.opportunities)|x.third_down_conversions.gt(x.third_down_opportunities)|x.opportunities.ne(x.rushes+x.targets))
        if bad.any():raise ValueError('invalid source opportunity counts '+path.name)
        constraints.append({'name':path.name,'rows':len(x),'count_constraints_pass':True})
    return {'schema':'pp-scouting-depth-audit/1','unique_public_archives':len(catalog),'public_bytes':sum(s['bytes'] for s in catalog.values()),'public_sources':list(catalog.values()),'unavailable_requested_sources':failures,'nfl_performance_coverage':coverage,'opportunity_count_constraints':constraints,'primary_and_pressure_labels_preserved':True,'older_unobserved_snap_pressure_labels_remain_missing':True,'expanded_players':len(v),'added_older_prospects':len(old),'proprietary_or_historical_tracking_acquisition_claimed':False}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--cache',type=Path,required=True);p.add_argument('--original',type=Path,required=True);p.add_argument('--extended',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();r=audit(a.cache,a.original,a.extended);a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ('public_sources','opportunity_count_constraints','nfl_performance_coverage','unavailable_requested_sources')}))
