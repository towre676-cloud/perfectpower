#!/usr/bin/env python3
"""Replay hash-audited identity and availability ledgers from frozen public bytes."""
import argparse,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np
import pandas as pd
from perfectpower.scouting_identity import roster_identity,contextual_recruits,strict_name

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def clean(obj):
    if isinstance(obj,dict):return {str(k):clean(v) for k,v in obj.items()}
    if isinstance(obj,list):return [clean(v) for v in obj]
    if isinstance(obj,(np.integer,np.floating)):obj=obj.item()
    if isinstance(obj,float) and not np.isfinite(obj):return None
    return obj

def write(path,obj):path.write_text(json.dumps(clean(obj),indent=2,allow_nan=False)+'\n')

def build(cache,players,out,receipts):
    out.mkdir(parents=True,exist_ok=True);receipts.mkdir(parents=True,exist_ok=True)
    manifest=json.loads((cache/'acquisition.json').read_text());wanted={f'cfb_{kind}_{y}.parquet' for kind in ('rosters','recruits') for y in range(2014,2026)}
    entries={s['name']:s for s in manifest['sources'] if s['name'] in wanted and s['status']=='acquired'}
    if set(entries)!=wanted:raise ValueError('missing original archive manifest')
    audit=[]
    for name,src in sorted(entries.items()):
        if digest(cache/name)!=src['sha256'] or (cache/name).stat().st_size!=src['bytes']:raise ValueError('changed public archive '+name)
        audit.append(dict(src,observation_season=int(name[-12:-8]),retrieved_utc=manifest['retrieved_utc'],verified_published_at=None))
    # Earlier frozen roster receipts are checked too. They are exclusion evidence,
    # not additional recruiting features or retrospective rating snapshots.
    depth=json.loads((ROOT/'receipts/scouting_depth/source_audit.json').read_text())
    rosters=[]
    for src in depth['public_sources']:
        name=src['name']
        if name.startswith('cfb_rosters_'):
            if digest(cache/name)!=src['sha256']:raise ValueError('changed roster '+name)
            rosters.append(pd.read_parquet(cache/name))
    roster=pd.concat(rosters,ignore_index=True)
    recruits=pd.concat([pd.read_parquet(cache/f'cfb_recruits_{y}.parquet') for y in range(2014,2026)],ignore_index=True)
    unit=pd.read_pickle(players);ids=roster_identity(unit,roster)
    contexts=contextual_recruits(recruits,roster)
    ids.to_pickle(out/'prospect_identity.pkl');contexts.to_pickle(out/'recruit_context.pkl')
    contexts.to_json(out/'recruit_context.jsonl',orient='records',lines=True)
    ids.to_json(out/'prospect_identity.jsonl',orient='records',lines=True)
    # Only pre-draft rows attach to a prospect; later records never rescue a link.
    c=contexts[contexts.status.eq('corroborated_context_only')]
    links=ids[ids.status.eq('verified_name_birth')].merge(c,on='college_id',how='inner',validate='one_to_one')
    links=links[links.recruit_season.lt(links.draft_year)].copy()
    links=links[[bool([s for s in seasons if s < y]) for seasons,y in zip(links.context_evidence_seasons,links.draft_year)]].copy()
    links['authoritative_recruit_identity']=False;links['verified_published_at']=None
    links['pre_draft_feature_eligible']=False
    links.to_json(out/'prospect_recruit_context.jsonl',orient='records',lines=True)
    numeric=roster[['cfbd_recruit_ids','athlete_display_name']].dropna().copy();pairs=[]
    for row in numeric.itertuples(index=False):
        try:values=json.loads(str(row.cfbd_recruit_ids))
        except (ValueError,TypeError):continue
        for i in values:
            if str(i)!='0':pairs.append((str(i),strict_name(row.athlete_display_name)))
    cfbd=pd.DataFrame(pairs,columns=['recruit_id','roster_name']).drop_duplicates()
    accidental=recruits.assign(recruit_id=recruits.recruit_id.astype(str),recruit_name=recruits.player_name.map(strict_name)).merge(cfbd,on='recruit_id')
    # Conservative current-vintage identity view; blank rejected identities and
    # every identity-dependent inherited feature. Do not overwrite old studies.
    verified=dict(zip(ids.pfr_id,ids.college_id));repaired=unit.copy()
    repaired['espn_id']=repaired.pfr_id.map(verified)
    supported=ids.status.eq('verified_name_birth') & ids.college_id.eq(ids.previous_id)
    rejected=~repaired.pfr_id.isin(ids.loc[supported,'pfr_id'])
    affected=[x for x in repaired if x.startswith(('college_raw__','depth_raw__','depth_metric__','metric__college','metric__rush_','metric__receiving_','metric__passing_','metric__trend_'))]
    repaired.loc[rejected,affected]=np.nan
    for col in [x for x in repaired if x.startswith('_college_name_verified__')]:repaired.loc[rejected,col]=False
    opportunity=[]
    for row in repaired.to_dict('records'):
        if pd.isna(row['espn_id']):continue
        for lag in (1,2,3):
            cols={k:v for k,v in row.items() if k.startswith('depth_raw__') and k.endswith('__lag'+str(lag)) and pd.notna(v)}
            if cols:opportunity.append(dict(pfr_id=row['pfr_id'],college_id=int(row['espn_id']),draft_year=int(row['draft_year']),observation_season=int(row['draft_year'])-lag,counts=cols,source_vintage='2026-10-15; historical publication unverified',routes_or_pass_rush_denominator_available=False))
    (out/'college_opportunity.jsonl').write_text(''.join(json.dumps(clean(r),allow_nan=False)+'\n' for r in opportunity))
    repaired.to_pickle(out/'prospects_identity_guarded.pkl')
    has_context=set(links.pfr_id);ids['recruit_context']=ids.pfr_id.isin(has_context)
    source_coverage=[]
    for year,g in ids.groupby('draft_year'):
        source_coverage.append({'class':int(year),'players':len(g),'verified_college':int(g.status.eq('verified_name_birth').sum()),'context_recruit':int(g.recruit_context.sum()),'eligible_asof_recruit':0})
    by_pos={str(pos):{'players':len(g),'verified_college':int(g.status.eq('verified_name_birth').sum()),'context_recruit':int(g.recruit_context.sum())} for pos,g in ids.groupby('pos')}
    selection={}
    for target in ('target','receiving_efficiency','pressure_target'):
        a=unit[['pfr_id','draft_year',target]].merge(ids[['pfr_id','status','recruit_context']],on='pfr_id',validate='one_to_one')
        selection[target]={}
        for label,mask in [('all',pd.Series(True,index=a.index)),('verified_college',a.status.eq('verified_name_birth')),('context_recruit',a.recruit_context)]:
            g=a[mask];selection[target][label]={'players':len(g),'observed_outcomes':int(g[target].notna().sum()),'outcome_mean':None if g[target].notna().sum()==0 else float(g[target].mean())}
    # This audit deliberately reads outcomes only for selection diagnostics, after
    # all identity decisions are fixed. No matching rule uses them.
    outcome_selection_by_class={}
    for year,g in ids.groupby('draft_year'):
        a=unit[unit.draft_year.eq(year)].merge(g[['pfr_id','recruit_context']],on='pfr_id',validate='one_to_one')
        outcome_selection_by_class[str(year)]={}
        for target in ('target','receiving_efficiency','pressure_target'):
            outcome_selection_by_class[str(year)][target]={str(flag):{'players':len(h),'observed':int(h[target].notna().sum()),'mean':float(h[target].mean()) if h[target].notna().any() else None} for flag,h in a.groupby('recruit_context')}
    result={'schema':'pp-scouting-identity-audit/1','population':len(unit),'original_archives':audit,'original_archive_count':len(audit),
      'prospect_identity_status':ids.status.value_counts().to_dict(),'changed_or_cleared_previous_ids':int((ids.college_id.fillna(-1)!=ids.previous_id.fillna(-1)).sum()),
      'recruit_records':len(contexts),'recruit_context_status':contexts.status.value_counts().to_dict(),'prospects_with_context_recruit':len(links),
      'opportunity_player_season_records':len(opportunity),'inherited_feature_links_cleared':int(rejected.sum()),'authoritative_recruit_links':0,'historically_available_recruit_features':0,
      'numeric_namespace_collisions':len(accidental),'numeric_collision_name_disagreements':int(accidental.recruit_name.ne(accidental.roster_name).sum()),
      'coverage_by_class':source_coverage,'coverage_by_position':by_pos,'selection_diagnostics':selection,'selection_by_class':outcome_selection_by_class,
      'recruitment_adjusted_experiment':{'status':'blocked_by_identity_and_asof_evidence','invented_matches':False,'ratings_enter_models':False},
      'input_sha256':digest(players),'source_sha256':{str(p.relative_to(ROOT)):digest(p) for p in [Path(__file__),ROOT/'python/perfectpower/scouting_identity.py']},
      'ledger_sha256':{p.name:digest(p) for p in sorted(out.glob('*.jsonl'))},
      'limitations':['Corroborated exact name/school/year is not independently verified identity.','Roster name and birth evidence is current vintage, not original publication evidence.','Exact-name rules sacrifice coverage; transfers, spelling differences, missing birth dates and ambiguous people remain unresolved.','Drafted Combine invitees and observed NFL efficiency outcomes are selected populations.','No on-field routes, college pass-rush snaps, or true defensive opportunity denominators were established.']}
    write(receipts/'identity_audit.json',result);return result

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ('cache','players','out','receipts'):p.add_argument('--'+key,type=Path,required=True)
    a=p.parse_args()
    if ROOT in a.out.resolve().parents or ROOT==a.out.resolve():p.error('player ledgers must stay outside checkout')
    r=build(a.cache,a.players,a.out,a.receipts);print(json.dumps({k:r[k] for k in ['population','prospect_identity_status','recruit_context_status','prospects_with_context_recruit','numeric_namespace_collisions']}))
