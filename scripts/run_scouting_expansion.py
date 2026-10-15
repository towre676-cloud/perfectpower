#!/usr/bin/env python3
"""Chronological prospect evaluation; source features fixed before outcomes.

All published metrics are aggregate. Player predictions stay outside checkout.
Draft controls use observed draft pick and answer a separate post-draft question.
"""
import argparse,hashlib,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd
from perfectpower.scouting_metrics import feature_sets,tuned,optional_custom,chronological_splits


def metrics(rows,pred,baseline,seed=5481):
    y=rows.target.to_numpy();lp=(y-pred)**2;lb=(y-baseline)**2;gain=lb-lp
    rng=np.random.default_rng(seed);indices=np.column_stack([rng.choice(np.flatnonzero(rows.draft_year.to_numpy()==year),(4000,int(rows.draft_year.eq(year).sum())),replace=True) for year in sorted(rows.draft_year.unique())]);boot=gain[indices].mean(axis=1)
    return {'players':len(rows),'mse':float(lp.mean()),'baseline_mse':float(lb.mean()),'relative_gain':float(gain.mean()/lb.mean()),'absolute_gain':float(gain.mean()),'paired_player_bootstrap_95':np.quantile(boot,[.025,.975]).tolist(),'mean_absolute_error':float(np.abs(y-pred).mean()),'by_class':{str(year):{'players':len(g),'mse':float(lp[g.index].mean()),'baseline_mse':float(lb[g.index].mean()),'relative_gain':float(gain[g.index].mean()/lb[g.index].mean())} for year,g in rows.groupby('draft_year')},'interval_scope':'Fixed-prediction class-stratified paired player bootstrap; excludes refitting, model-bank research selection, historical source revisions and new-cohort shift.'}


def rank_diagnostics(rows,pred,baseline):
    sums=[]
    for _,g in rows.groupby(['draft_year','pos']):
        if len(g)<8:continue
        n=max(1,len(g)//4);idx=g.index.to_numpy();a=idx[np.argsort(-pred[idx],kind='stable')[:n]];b=idx[np.argsort(-baseline[idx],kind='stable')[:n]]
        sums.append((n,float(rows.loc[a,'two_season_snaps'].sum()),float(rows.loc[b,'two_season_snaps'].sum())))
    den=sum(s[0] for s in sums)
    return {'scope':'Diagnostic equal-count top quartile within position/class groups of at least eight prospects; actual NFL opportunity, not causal value or decision profit. Not used to tune models.','selected_players':den,'candidate_mean_snaps':sum(s[1] for s in sums)/den if den else None,'baseline_mean_snaps':sum(s[2] for s in sums)/den if den else None}


def evaluate(unit,out,target='target'):
    unit=unit.copy();unit['target']=unit[target];unit=unit[unit.target.notna()].copy();unit['log_pick']=np.log(unit.pick);unit=unit.reset_index(drop=True)
    available={f'availability__{c}':unit[c].notna().astype(float) for c in unit if c.startswith('college_raw__') or c.startswith('metric__college') or c.startswith(('metric__rush_','metric__receiving_','metric__passing_'))}
    unit=pd.concat([unit,pd.DataFrame(available,index=unit.index)],axis=1)
    specs=feature_sets(unit);records=[];audits=[];skipped=[]
    for year in range(2018,2025):
        train=unit[unit.draft_year.le(year-2)].reset_index(drop=True);test=unit[unit.draft_year.eq(year)].reset_index(drop=True)
        if len(test)<10 or not chronological_splits(train):
            skipped.append({'class':year,'train_players':len(train),'test_players':len(test),'reason':'insufficient matured chronological inner classes or evaluation players'});continue
        pp={};a={'class':year,'train_players':len(train),'test_players':len(test),'latest_training_class':int(train.draft_year.max()),'configs':{}}
        for name in ('combine','availability','broad_raw','draft_control'):
            pp[name],a['configs'][name]=tuned(train,test,specs[name])
        for name,base in [('custom','broad_raw'),('draft_control_custom','draft_control')]:
            pp[name],a['configs'][name]=optional_custom(train,test,specs[base],specs[name])
        q=test[['pfr_id','draft_year','pos','target','two_season_snaps']].copy()
        for name,v in pp.items():q[name]=v
        records.append(q);audits.append(a);print(json.dumps({'stage':'outer','target':target,'class':year,'train_players':len(train),'test_players':len(test),'custom_shrinkage':a['configs']['custom']['shrinkage']}),flush=True)
    if not records:return {'target':target,'status':'insufficient chronological coverage','skipped':skipped}
    rows=pd.concat(records,ignore_index=True);rows.to_pickle(out/(target+'_predictions.pkl'))
    comparisons={}
    for candidate,base in [('availability','combine'),('broad_raw','availability'),('broad_raw','combine'),('custom','broad_raw'),('custom','combine'),('draft_control','broad_raw'),('draft_control_custom','draft_control')]:
        key=candidate+'_vs_'+base;comparisons[key]=metrics(rows,rows[candidate].to_numpy(),rows[base].to_numpy());comparisons[key]['ranking_diagnostic']=rank_diagnostics(rows,rows[candidate].to_numpy(),rows[base].to_numpy())
    return {'target':target,'status':'evaluated','eligible_population':len(unit),'evaluated_players':len(rows),'feature_dimensions':{k:len(v) for k,v in specs.items()},'outer_audits':audits,'skipped':skipped,'comparisons':comparisons,'positions':{str(k):int(v) for k,v in rows.groupby('pos').size().items()},'classes':[int(y) for y in sorted(rows.draft_year.unique())],'maturity_gap_years':2}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--players',type=Path,required=True);p.add_argument('--private-out',type=Path,required=True);p.add_argument('--aggregate',type=Path,required=True);a=p.parse_args()
    if ROOT==a.private_out.resolve() or ROOT in a.private_out.resolve().parents:p.error('private output must be outside source checkout')
    a.private_out.mkdir(parents=True,exist_ok=True);start=time.perf_counter();u=pd.read_pickle(a.players)
    r={'schema':'pp-scouting-expanded-evaluation/1','protocol_sha256':hashlib.sha256((ROOT/'docs/SCOUTING_EXPANSION_PROTOCOL.json').read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(a.players.read_bytes()).hexdigest(),'primary':evaluate(u,a.private_out),'secondary':evaluate(u,a.private_out,'pressure_target'),'retrospective_only':True,'causal_or_prospective_claim':False}
    matched=u[u[[f'_college_name_verified__lag{k}' for k in (1,2,3)]].any(axis=1)].copy();dest=a.private_out/'college_matched';dest.mkdir(exist_ok=True);r['college_matched_primary']=evaluate(matched,dest)
    r['elapsed_seconds']=time.perf_counter()-start
    r['source_sha256']={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [ROOT/'python/perfectpower/scouting_metrics.py',Path(__file__).resolve()]};a.aggregate.parent.mkdir(parents=True,exist_ok=True);a.aggregate.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'primary':r['primary'].get('evaluated_players'),'secondary':r['secondary'].get('evaluated_players')}))
if __name__=='__main__':main()
