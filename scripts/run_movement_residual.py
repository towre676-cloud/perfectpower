#!/usr/bin/env python3
"""Reproduce nested residual corrections from authorized private checkpoints.

Never publishes player rows. Input is players.pkl/events.pkl from the existing
movement transfer extractor, plus source combine_position on players. Requires
unique player rows. Outputs only aggregates to --aggregate; all predictions go
to an explicit --private-out directory outside the source checkout.
"""
import argparse,hashlib,json,platform,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd, sklearn
from perfectpower.movement_residual import fit_predict,splits,FAMILY_NAMES,validate


def summary(rows,pred,seed=717,draws=4000):
    y=rows.target.to_numpy();base=(y-pred['conventional'])**2;rng=np.random.default_rng(seed)
    # Average repeated outer squared losses before calling this helper when used
    # with development repeats: bootstrap players, never fold appearances.
    return loss_summary(rows,{k:(y-v)**2 for k,v in pred.items()},seed,draws)


def loss_summary(rows,loss,seed=717,draws=4000):
    rng=np.random.default_rng(seed);base=np.asarray(loss['conventional']);groups=[np.flatnonzero(rows.draft_year.to_numpy()==c) for c in sorted(rows.draft_year.unique())]
    indices=np.column_stack([rng.choice(g,(draws,len(g)),replace=True) for g in groups])
    result={'players':len(rows),'baseline_mse':float(base.mean()),'comparisons':{}}
    for name,l in loss.items():
        if name=='conventional':continue
        d=base-l;boot=d[indices].mean(axis=1)
        result['comparisons'][name]={'mse':float(np.mean(l)),'absolute_gain':float(d.mean()),'relative_gain':float(d.mean()/base.mean()),'paired_player_bootstrap_95':np.quantile(boot,[.025,.975]).tolist(),'player_win_fraction':float(np.mean(d>0)), 'by_class':{str(c):{'players':len(g),'baseline_mse':float(base[g].mean()),'candidate_mse':float(np.mean(l[g])),'relative_gain':float(d[g].mean()/base[g].mean())} for c,g in zip(sorted(rows.draft_year.unique()),groups)}}
    result['interval_scope']='Fixed fitted predictions; class-stratified paired players. Does not include refitting, adaptive research selection or new-cohort uncertainty.'
    return result


def evaluate(unit,events,out,refits=100):
    validate(unit)
    if unit.nfl_id.duplicated().any():raise ValueError('expected one row per player')
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    dev=unit[unit.draft_year.isin([2023,2024])].reset_index(drop=True);future=unit[unit.draft_year.eq(2025)].reset_index(drop=True)
    result={'schema':'pp-movement-residual/1','protocol_sha256':hashlib.sha256((ROOT/'docs/MOVEMENT_RESIDUAL_PROTOCOL.json').read_bytes()).hexdigest(),'prior_2025_inspection':True,'scope':'All classes previously inspected; conditional rookie participation target; development study, no untouched validation.','repeats':[],'temporal':{}}
    losses=[]
    for seed in (714,914,1114):
        pred={k:np.zeros(len(dev)) for k in ('conventional',)+FAMILY_NAMES+('selected',)};audits=[]
        for fold,(i,j) in enumerate(splits(dev,4,seed)):
            p,a=fit_predict(dev.iloc[i],dev.iloc[j],events,seed+fold)
            for k,v in p.items():pred[k][j]=v
            a['fold']=fold;audits.append(a)
            print(json.dumps({'stage':'nested','seed':seed,'fold':fold}),flush=True)
        loss={k:np.square(dev.target.to_numpy()-v) for k,v in pred.items()};losses.append(loss)
        result['repeats'].append({'seed':seed,'evaluation':loss_summary(dev,loss),'outer_audits':audits})
        private=dev[['nfl_id','draft_year','target']].copy()
        for k,v in pred.items():private[k]=v
        private.to_pickle(out/f'nested_{seed}.pkl')
    result['development']=loss_summary(dev,{k:np.mean([l[k] for l in losses],axis=0) for k in losses[0]})
    for label,tr,te in [('2023_to_2024',dev[dev.draft_year.eq(2023)],dev[dev.draft_year.eq(2024)]),('exploratory_2025',dev,future)]:
        tr=tr.reset_index(drop=True);te=te.reset_index(drop=True)
        p,a=fit_predict(tr,te,events,1714);result['temporal'][label]={'evaluation':summary(te,p),'audit':a}
        private=te[['nfl_id','draft_year','target']].copy()
        for k,v in p.items():private[k]=v
        private.to_pickle(out/f'{label}.pkl')
        # Entire estimator, preprocessing, baseline and correction selection refit.
        # Duplicate resampled identities are assigned together in all folds.
        gains=[];zero=0;rng=np.random.default_rng(2714);private_refits=[]
        for b in range(refits):
            ix=np.concatenate([rng.choice(g.index,len(g),replace=True) for _,g in tr.groupby('draft_year')])
            train=tr.iloc[ix].reset_index(drop=True)
            pp,aa=fit_predict(train,te,events,1714)
            test_ix=np.concatenate([rng.choice(g.index,len(g),replace=True) for _,g in te.groupby('draft_year')])
            y=te.target.to_numpy();lb=np.square(y-pp['conventional']);lc=np.square(y-pp['selected'])
            gains.append(float(np.mean((lb-lc)[test_ix])));zero+=aa['selection']['selected']['config'][0]=='zero'
            private_refits.append((pp['conventional'],pp['selected']))
            if (b+1)%10==0:print(json.dumps({'stage':'full_refit','comparison':label,'done':b+1,'total':refits}),flush=True)
        np.savez_compressed(out/(label+'_refits.npz'),predictions=np.array(private_refits))
        result['temporal'][label]['full_refit_bootstrap']={'draws':refits,'absolute_gain_95':np.quantile(gains,[.025,.975]).tolist() if gains else None,'mean_absolute_gain':float(np.mean(gains)) if gains else None,'positive_gain_fraction':float(np.mean(np.array(gains)>0)) if gains else None,'zero_selection_count':zero,'scope':'Class-stratified training-player resample and complete nested refit, then paired test-player resample. Conditional on existing classes; not new-cohort or researcher-selection uncertainty.'}
    result['source_support']={'players':len(unit),'by_class':{str(k):int(v) for k,v in unit.groupby('draft_year').size().items()},'attempts':len(events),'missing_fraction_by_family':{name:float(unit[cols].isna().to_numpy().mean()) for name,cols in __import__('perfectpower.movement_residual',fromlist=['families']).families(unit).items()}}
    return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--players',type=Path,required=True);p.add_argument('--events',type=Path,required=True);p.add_argument('--private-out',type=Path,required=True);p.add_argument('--aggregate',type=Path,required=True);p.add_argument('--refits',type=int,default=100);a=p.parse_args()
    if a.refits<0:p.error('--refits must be nonnegative')
    if ROOT==a.private_out.resolve() or ROOT in a.private_out.resolve().parents:p.error('--private-out must be outside repository')
    start=time.perf_counter();r=evaluate(pd.read_pickle(a.players),pd.read_pickle(a.events),a.private_out,a.refits)
    r['input_sha256']={k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in [('players',a.players),('events',a.events)]}
    r['source_sha256']={str(v.relative_to(ROOT)):hashlib.sha256(v.read_bytes()).hexdigest() for v in [ROOT/'python/perfectpower/movement_residual.py',Path(__file__).resolve()]}
    r['versions']={'python':platform.python_version(),'numpy':np.__version__,'pandas':pd.__version__,'sklearn':sklearn.__version__};r['elapsed_seconds']=time.perf_counter()-start
    a.aggregate.parent.mkdir(parents=True,exist_ok=True);a.aggregate.write_text(json.dumps(r,indent=2,allow_nan=False)+'\n');print(json.dumps(r['development']),flush=True)
if __name__=='__main__':main()
