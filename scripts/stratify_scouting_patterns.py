#!/usr/bin/env python3
"""Stratify the preserved experiment without subgroup model selection."""
import argparse,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np
import pandas as pd
from perfectpower.scouting_identity import EXPERTS
from perfectpower.scouting_depth import GROUPS
from perfectpower.scouting_metrics import RAW_COMBINE
from perfectpower.scouting_patterns import validate,group_masks,loss_summary,simultaneous_intervals,mechanisms,influence,exposure_metrics,common_support_contrast,matured_role_mean
TASKS=('target','receiving_efficiency','pressure_target')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(x):
    if isinstance(x,dict):return {str(k):safe(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [safe(v) for v in x]
    if isinstance(x,(np.integer,np.floating,np.bool_)):x=x.item()
    if isinstance(x,float) and not np.isfinite(x):return None
    return x

def run(players,identity,predictions,cache,out,receipt):
    out.mkdir(parents=True,exist_ok=True);u=pd.read_pickle(players);ids=pd.read_pickle(identity/'prospect_identity.pkl');links=pd.read_json(identity/'prospect_recruit_context.jsonl',lines=True)
    # Explicit source hash verification precedes denominator extraction.
    source=json.loads((ROOT/'receipts/scouting_depth/source_audit.json').read_text());snaps=[];source_receipts=[]
    for s in source['public_sources']:
        if s['name'].startswith('snap_counts_') and int(s['name'][12:16])>=2013:
            p=cache/s['name']
            if sha(p)!=s['sha256']:raise ValueError('changed defensive opportunity source '+p.name)
            d=pd.read_csv(p,usecols=['season','game_type','pfr_player_id','defense_snaps']);snaps.append(d[d.game_type.eq('REG')]);source_receipts.append(s)
    snap=pd.concat(snaps,ignore_index=True).groupby(['pfr_player_id','season']).defense_snaps.sum()
    exposure={}
    for row in u.itertuples():
        keys=[(row.pfr_id,y) for y in (row.draft_year,row.draft_year+1)];exposure[row.pfr_id]=sum(snap.get(k,0.) for k in keys) if row.draft_year>=2013 else np.nan
    meta=u[['pfr_id','player_name','nfl_receiving_targets']].copy();meta['defensive_snaps']=meta.pfr_id.map(exposure)
    meta['identity_status']=meta.pfr_id.map(ids.set_index('pfr_id').status);meta['recruit_context']=meta.pfr_id.isin(set(links.pfr_id))
    raw=[c for c in u if c.startswith(('college_raw__','depth_raw__'))]
    meta['college_seasons']=sum(u[[c for c in raw if c.endswith('__lag'+str(lag))]].notna().any(axis=1).astype(int) for lag in (1,2,3))
    missing=u[RAW_COMBINE].isna().sum(axis=1);meta['combine_missing']=pd.cut(missing,[-1,0,2,np.inf],labels=['0','1-2','3+']).astype(str)
    result={'schema':'pp-scouting-patterns/1','retrospective_development':True,'models_selected_or_promoted':False,'historical_prediction_identity_version':'Original scouting-depth frozen forecasts; strict identity categories describe their support, not a refit using guarded inputs.',
      'protocol_sha256':sha(ROOT/'docs/SCOUTING_PATTERNS_PROTOCOL.json'),'input_sha256':{'players':sha(players),'identity':sha(identity/'prospect_identity.pkl'),'recruit_context':sha(identity/'prospect_recruit_context.jsonl')},'denominator_sources':source_receipts,'tasks':{}}
    for task in TASKS:
        path=predictions/(task+'_aggregate.pkl');q=pd.read_pickle(path)[['pfr_id','draft_year','pos','target','aggregate',*EXPERTS]].merge(meta,on='pfr_id',validate='one_to_one').reset_index(drop=True);validate(q)
        q['role']=q.pos.map(GROUPS).fillna(q.pos)
        q['identity_verified']=q.identity_status.eq('verified_name_birth')
        if task=='pressure_target':
            reconstructed=q.target*q.defensive_snaps/100
            if not q.defensive_snaps.gt(0).all() or not np.allclose(reconstructed,np.round(reconstructed),atol=1e-7,rtol=0):raise ValueError('pressure denominator reconstruction failed')
        if task=='receiving_efficiency' and not q.nfl_receiving_targets.ge(30).all():raise ValueError('receiving target threshold failed')
        cv=q[list(EXPERTS)].std(axis=1,ddof=0)/(1+q['combine'].abs());q['disagreement_band']=pd.cut(cv,[-np.inf,.1,.25,np.inf],labels=['<0.1','0.1-0.25','>=0.25'],right=False).astype(str)
        q['correction_direction']=np.where(q['aggregate']<q['combine'],'lower','higher_or_equal')
        bins={'target':[-np.inf,np.log1p(500),np.log1p(2000),np.log1p(4000),np.inf],'receiving_efficiency':[-np.inf,6,8,10,np.inf],'pressure_target':[-np.inf,1,2,3,np.inf]}[task]
        q['prediction_band']=pd.cut(q['combine'],bins,right=False).astype(str);q['outcome_band']=pd.cut(q.target,bins,right=False).astype(str)
        q['exposure']=q.defensive_snaps if task=='pressure_target' else q.nfl_receiving_targets if task=='receiving_efficiency' else np.nan
        ebins=[0,250,1000,np.inf] if task=='pressure_target' else [0,60,120,np.inf]
        q['exposure_band']=pd.cut(q.exposure,ebins,include_lowest=True,right=False).astype(str).replace('nan','missing')
        training=u[['pfr_id','draft_year','pos',task]].rename(columns={task:'label'}).copy();training['role']=training.pos.map(GROUPS).fillna(training.pos)
        q['role_mean'],control_audit=matured_role_mean(training,q)
        control=q.copy();control['aggregate']=q.role_mean
        masks=group_masks(q,task);intervals,interval_info=simultaneous_intervals(q,masks)
        groups={}
        for name,(mask,outcome_only) in masks.items():
            s=loss_summary(q.loc[mask]);s['outcome_conditioned_not_a_routing_feature']=outcome_only;s['uncertainty']=intervals.get(name);s['exposure_weighted']=exposure_metrics(q.loc[mask]);s['role_mean_control']=loss_summary(control.loc[mask]);groups[name]=s
        inf,ordered=influence(q);ordered.to_json(out/(task+'_player_influence.jsonl'),orient='records',lines=True)
        q.to_pickle(out/(task+'_strata.pkl'))
        result['tasks'][task]={'players':len(q),'prediction_sha256':sha(path),'groups':groups,'simultaneous_intervals':interval_info,'mechanism':mechanisms(q),'influence':inf,'exposure_weighted':exposure_metrics(q),'selection_contrasts':{'identity':common_support_contrast(q,'identity_verified'),'recruit_context_within_verified':common_support_contrast(q[q.identity_verified],'recruit_context')},'pressure_count_reconstruction_checked':task=='pressure_target','role_mean_control':{'summary':loss_summary(control),'training_audit':control_audit},'exploratory_LB_lower_sensitivity':influence(q[q.pos.eq('LB')&q.correction_direction.eq('lower')])[0] if task=='pressure_target' else None}
        print(json.dumps({'task':task,'groups':len(groups),'all':groups['all'],'exposure':result['tasks'][task]['exposure_weighted']}),flush=True)
    result['source_sha256']={str(p.relative_to(ROOT)):sha(p) for p in [Path(__file__),ROOT/'python/perfectpower/scouting_patterns.py']}
    receipt.parent.mkdir(parents=True,exist_ok=True);receipt.write_text(json.dumps(safe(result),indent=2,allow_nan=False)+'\n');return result
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ('players','identity','predictions','cache','out','receipt'):p.add_argument('--'+key,type=Path,required=True)
    a=p.parse_args();run(**vars(a))
