#!/usr/bin/env python3
"""Whole-player development and forward tests of source launch to NFL get-off."""
import argparse,hashlib,json,platform,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd,sklearn
from perfectpower.combine_getoff import fit_predict,player_loss
from perfectpower.movement_residual import splits
MODELS=('raw_mean','raw_conventional','context','conventional','fixed','selected')

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def loss_tables(rows,pred):
    primary=pd.DataFrame({k:player_loss(rows,p) for k,p in pred.items()})
    auxiliary=pd.DataFrame({k:pd.Series((rows.player_get_off.to_numpy()-p)**2,index=rows.index).groupby(rows.nfl_id).mean() for k,p in pred.items()})
    return primary,auxiliary

def summarize(meta,loss):
    meta=meta.set_index('nfl_id').reindex(loss.index);base=loss.conventional.to_numpy();rng=np.random.default_rng(717)
    groups=[np.flatnonzero(meta.draft_year.to_numpy()==y) for y in sorted(meta.draft_year.unique())];sample=np.column_stack([rng.choice(g,size=(4000,len(g)),replace=True) for g in groups])
    r={'players':len(meta),'baseline_mse_seconds2':float(base.mean()),'comparisons':{}}
    for key in MODELS:
        if key=='conventional':continue
        delta=base-loss[key].to_numpy()
        r['comparisons'][key]={'mse_seconds2':float(loss[key].mean()),'relative_gain':float(delta.mean()/base.mean()) if base.mean()>0 else None,'absolute_gain_seconds2':float(delta.mean()),'conditional_player_95':np.quantile(delta[sample].mean(axis=1),[.025,.975]).tolist(),'by_class':{str(y):{'players':int((meta.draft_year==y).sum()),'relative_gain':float(delta[meta.draft_year.to_numpy()==y].mean()/base[meta.draft_year.to_numpy()==y].mean())} for y in sorted(meta.draft_year.unique())}}
    r['scope']='Equal-player loss and fixed-prediction class-stratified paired bootstrap; no refitting, shared-game, researcher-selection or new-cohort guarantee.'
    return r

def evaluate(rows,out):
    if len(rows)!=14665 or rows.groupby('draft_year').nfl_id.nunique().to_dict()!={2023:23,2024:22,2025:29}:raise ValueError('fixed74-player14665-rush cohort required')
    out.mkdir(parents=True,exist_ok=True);dev=rows[rows.draft_year.isin([2023,2024])].reset_index(drop=True);future=rows[rows.draft_year.eq(2025)].reset_index(drop=True);metadata=dev[['nfl_id','draft_year']].drop_duplicates()
    r={'schema':'pp-combine-getoff/1','protocol_sha256':sha(ROOT/'docs/COMBINE_GETOFF_PROTOCOL.json'),'independent_confirmation':False,'models_promoted':False,'sealed_two_season_outcomes_opened':False,'cohort':{'players':rows.nfl_id.nunique(),'rushes':len(rows),'by_class':{str(k):int(v) for k,v in rows.groupby('draft_year').nfl_id.nunique().items()}},'repeats':[],'temporal':{}}
    primary=[];auxiliary=[]
    for seed in (714,914,1114):
        pred={k:np.empty(len(dev)) for k in MODELS};audits=[]
        for f,(i,j) in enumerate(splits(dev,4,seed)):
            p,a=fit_predict(dev.iloc[i],dev.iloc[j],seed+f)
            for k,v in p.items():pred[k][j]=v
            audits.append(a);print(json.dumps({'stage':'nested','seed':seed,'fold':f,'apply':a['apply_correction']}),flush=True)
        p,a=loss_tables(dev,pred);primary.append(p);auxiliary.append(a)
        r['repeats'].append({'seed':seed,'primary':summarize(metadata,p),'auxiliary':summarize(metadata,a),'audits':audits})
        saved=dev[['game_id','play_id','nfl_id','draft_year','player_get_off']].copy()
        for k,v in pred.items():saved[k]=v
        saved.to_pickle(out/f'nested_{seed}.pkl')
    r['development']={'primary':summarize(metadata,sum(primary)/len(primary)),'auxiliary':summarize(metadata,sum(auxiliary)/len(auxiliary))}
    for label,tr,te in [('2023_to_2024',dev[dev.draft_year.eq(2023)],dev[dev.draft_year.eq(2024)]),('exploratory_2025',dev,future)]:
        tr=tr.reset_index(drop=True);te=te.reset_index(drop=True);p,a=fit_predict(tr,te,1714);loss,aux=loss_tables(te,p);meta=te[['nfl_id','draft_year']].drop_duplicates()
        r['temporal'][label]={'primary':summarize(meta,loss),'auxiliary':summarize(meta,aux),'audit':a}
        saved=te[['game_id','play_id','nfl_id','draft_year','player_get_off']].copy()
        for k,v in p.items():saved[k]=v
        saved.to_pickle(out/f'{label}.pkl');print(json.dumps({'stage':'temporal','label':label,'selected_gain':r['temporal'][label]['primary']['comparisons']['selected']['relative_gain']}),flush=True)
    return r
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ['rushes','private-out','aggregate']:p.add_argument('--'+key,type=Path,required=True)
    a=p.parse_args()
    if a.private_out.resolve()==ROOT or ROOT in a.private_out.resolve().parents:p.error('private outputs must stay outside checkout')
    t=time.perf_counter();r=evaluate(pd.read_pickle(a.rushes),a.private_out);r['input_sha256']=sha(a.rushes);r['source_sha256']={str(p.relative_to(ROOT)):sha(p) for p in [ROOT/'python/perfectpower/combine_getoff.py',Path(__file__)]};r['versions']={'python':platform.python_version(),'numpy':np.__version__,'pandas':pd.__version__,'sklearn':sklearn.__version__};r['elapsed_seconds']=time.perf_counter()-t;a.aggregate.parent.mkdir(parents=True,exist_ok=True);a.aggregate.write_text(json.dumps(r,indent=2,allow_nan=False)+'\n')
