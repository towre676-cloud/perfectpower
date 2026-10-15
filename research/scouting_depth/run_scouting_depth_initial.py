#!/usr/bin/env python3
"""Frozen chronological comparison of source metrics and nonlinear baselines."""
import argparse,hashlib,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd
from perfectpower.scouting_metrics import chronological_splits
from perfectpower.scouting_depth import tune,specs,BANK
from run_scouting_expansion import metrics


def compare(rows,candidate,base):
    r=metrics(rows,rows[candidate].to_numpy(),rows[base].to_numpy());year=rows.draft_year.to_numpy();delta=((rows.target-rows[base])**2-(rows.target-rows[candidate])**2).to_numpy();b=((rows.target-rows[base])**2).to_numpy();years=sorted(set(year));rng=np.random.default_rng(84593)
    # A class bootstrap respects dependence within a draft cohort. With only
    # seven classes this is a diagnostic, not a precise new-cohort guarantee.
    means=np.array([delta[year==y].mean() for y in years]);boot=means[rng.integers(0,len(years),(10000,len(years)))].mean(axis=1)
    r['equal_class_mean_absolute_gain']=float(means.mean());r['class_bootstrap_95_absolute_gain']=np.quantile(boot,[.025,.975]).tolist()
    r['leave_one_class_out_relative_gain']={str(y):float(delta[year!=y].mean()/b[year!=y].mean()) for y in years if len(years)>1}
    r['by_position']={str(pos):{'players':int(len(g)),'relative_gain':float(delta[g.index].mean()/b[g.index].mean())} for pos,g in rows.groupby('pos')}
    return r


def evaluate(unit,out,target):
    rows=unit[unit[target].notna()].copy();rows['target']=rows[target];rows['log_pick']=np.log(rows.pick);rows=rows.reset_index(drop=True);features=specs(rows);records=[];audits=[];skipped=[]
    for year in range(2018,2025):
        tr=rows[rows.draft_year.le(year-2)].reset_index(drop=True);te=rows[rows.draft_year.eq(year)].reset_index(drop=True)
        if len(te)<10 or not chronological_splits(tr):skipped.append(year);continue
        q=te[['pfr_id','draft_year','pos','target']].copy();q=q.reset_index(drop=True);config={};loss={}
        for family,cols in features.items():
            q[family],config[family],loss[family]=tune(tr,te,cols)
        for prefix in ('','draft_'):
            base=prefix+'raw';custom=prefix+'custom';gain=loss[base]-loss[custom];se=float(gain.std(ddof=1)/np.sqrt(len(gain)));accept=bool(gain.mean()>se)
            q[prefix+'optional']=q[custom] if accept else q[base];config[prefix+'optional']={'accept_custom':accept,'inner_paired_gain':float(gain.mean()),'inner_player_se':se}
        records.append(q);audits.append({'class':year,'training_players':len(tr),'test_players':len(te),'configs':config});print(json.dumps({'target':target,'class':year,'players':len(te),'selected':{k:v.get('selected',v) for k,v in config.items()}}),flush=True)
    if not records:return {'status':'insufficient matured classes','eligible':len(rows),'skipped':skipped}
    pred=pd.concat(records,ignore_index=True);pred.to_pickle(out/(target+'_predictions.pkl'))
    pairs=[('historical','combine'),('raw','combine'),('raw','historical'),('custom','raw'),('optional','raw'),('optional','combine'),('draft_raw','raw'),('draft_custom','draft_raw'),('draft_optional','draft_raw')]
    return {'status':'evaluated','eligible':len(rows),'evaluated':len(pred),'feature_dimensions':{k:len(v) for k,v in features.items()},'outer_audits':audits,'skipped':skipped,'comparisons':{c+'_vs_'+b:compare(pred,c,b) for c,b in pairs}}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--players',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--aggregate',type=Path,required=True);p.add_argument('--targets',nargs='+',choices=['target','receiving_efficiency','pressure_target'],default=['target','receiving_efficiency','pressure_target']);a=p.parse_args()
    if ROOT==a.out.resolve() or ROOT in a.out.resolve().parents:p.error('predictions must stay outside checkout')
    a.out.mkdir(parents=True,exist_ok=True);u=pd.read_pickle(a.players);start=time.perf_counter();r={'schema':'pp-scouting-depth-evaluation/1','protocol_sha256':hashlib.sha256((ROOT/'docs/SCOUTING_DEPTH_PROTOCOL.json').read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(a.players.read_bytes()).hexdigest(),'model_bank':BANK,'retrospective':True,'untouched_confirmation':False}
    for target in a.targets:
        r[target]=evaluate(u,a.out,target);a.aggregate.parent.mkdir(parents=True,exist_ok=True);a.aggregate.write_text(json.dumps(r,indent=2)+'\n')
    r['elapsed_seconds']=time.perf_counter()-start;r['source_sha256']={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [ROOT/'python/perfectpower/scouting_depth.py',Path(__file__).resolve()]};a.aggregate.write_text(json.dumps(r,indent=2)+'\n')
