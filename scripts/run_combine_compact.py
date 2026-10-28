#!/usr/bin/env python3
"""Run fixed compact Combine experiment on preserved private player inputs."""
import argparse,hashlib,json,platform,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd,sklearn
from perfectpower.combine_compact import COLUMNS,fit_predict
from perfectpower.movement_residual import splits,validate
from run_movement_residual import loss_summary

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def summary(rows,pred):return loss_summary(rows,{k:(rows.target.to_numpy()-v)**2 for k,v in pred.items()})

def run(unit,events,out,refits=20,permutations=16):
    validate(unit)
    if unit.nfl_id.duplicated().any():raise ValueError('one row per player required')
    if unit.groupby('draft_year').size().to_dict()!={2023:23,2024:22,2025:29} or len(unit)!=74 or int(unit.exposure.sum())!=14665 or len(events)!=361:raise ValueError('fixed cohort must match74 players/361 attempts/14665 rushes with23/22/29 classes')
    if not set(zip(events.nfl_id,events.draft_year))<=set(zip(unit.nfl_id,unit.draft_year)):raise ValueError('unmatched source attempt identity')
    if not set(COLUMNS)<=set(unit):raise ValueError('missing compact source coordinates')
    if not {'nfl_id','draft_year','event_id','drill_name'}<=set(events):raise ValueError('attempt provenance required')
    if events.duplicated(['nfl_id','draft_year','event_id']).any():raise ValueError('duplicate attempt')
    # The narrow experiment consumes saved source features, not fresh labels.
    for col in COLUMNS:
        _,drill,feature=col.split('__',2)
        values=events[events.drill_name.eq(drill)].groupby(['nfl_id','draft_year'])[feature].median()
        actual=np.array([values.get((r.nfl_id,r.draft_year),np.nan) for r in unit.itertuples()])
        if not np.allclose(actual,unit[col],equal_nan=True,rtol=1e-10,atol=1e-12):raise ValueError('player/attempt mismatch '+col)
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    dev=unit[unit.draft_year.isin([2023,2024])].reset_index(drop=True);future=unit[unit.draft_year.eq(2025)].reset_index(drop=True)
    result={'schema':'pp-combine-compact/1','protocol_sha256':sha(ROOT/'docs/COMBINE_COMPACT_PROTOCOL.json'),'independent_confirmation':False,'models_promoted':False,'sealed_two_season_outcomes_opened':False,'cohort':{'players':len(unit),'attempts':len(events),'rushes':int(unit.exposure.sum()),'by_class':{str(k):int(v) for k,v in unit.groupby('draft_year').size().items()},'source_position_counts':{str(k):int(v) for k,v in unit.groupby('combine_position').size().items()}},'repeats':[],'temporal':{},'feature_source_medians_verified':True}
    all_loss=[]
    for seed in (714,914,1114):
        pred={k:np.empty(len(dev)) for k in ('conventional','global_mean','role_mean','fixed','selected')};audits=[]
        for f,(i,j) in enumerate(splits(dev,4,seed)):
            pp,a=fit_predict(dev.iloc[i],dev.iloc[j],seed+f)
            for k,v in pp.items():pred[k][j]=v
            audits.append(a)
        loss={k:(dev.target.to_numpy()-v)**2 for k,v in pred.items()};all_loss.append(loss)
        result['repeats'].append({'seed':seed,'evaluation':loss_summary(dev,loss),'audits':audits})
        private=dev[['nfl_id','draft_year','target']].copy()
        for k,v in pred.items():private[k]=v
        private.to_pickle(out/f'nested_{seed}.pkl')
        print(json.dumps({'stage':'nested','seed':seed,'selected_gain':result['repeats'][-1]['evaluation']['comparisons']['selected']['relative_gain']}),flush=True)
    result['development']=loss_summary(dev,{k:np.mean([x[k] for x in all_loss],axis=0) for k in all_loss[0]})
    for label,tr,te in [('2023_to_2024',dev[dev.draft_year.eq(2023)],dev[dev.draft_year.eq(2024)]),('exploratory_2025',dev,future)]:
        tr=tr.reset_index(drop=True);te=te.reset_index(drop=True);pp,a=fit_predict(tr,te,1714)
        result['temporal'][label]={'evaluation':summary(te,pp),'audit':a}
        uncertainty_rng=np.random.default_rng(717);resample=uncertainty_rng.integers(len(te),size=(4000,len(te)))
        bl=(te.target.to_numpy()-pp['conventional'])**2
        for name in pp:
            if name!='conventional':
                delta=bl-(te.target.to_numpy()-pp[name])**2
                result['temporal'][label]['evaluation']['comparisons'][name]['conditional_bonferroni_95']=np.quantile(delta[resample].mean(axis=1),[.05/16,1-.05/16]).tolist()
        private=te[['nfl_id','draft_year','target']].copy()
        for k,v in pp.items():private[k]=v
        private.to_pickle(out/f'{label}.pkl')
        rng=np.random.default_rng(2714);gains={k:[] for k in pp if k!='conventional'};zeros=0;max_change=0.;arrays=[]
        for b in range(refits):
            ix=np.concatenate([rng.choice(g.index,len(g),replace=True) for _,g in tr.groupby('draft_year')]);sample=tr.iloc[ix].reset_index(drop=True)
            bp,ba=fit_predict(sample,te,1714);jx=rng.integers(len(te),size=len(te));base=(te.target.to_numpy()-bp['conventional'])**2
            for k in gains:gains[k].append(float(np.mean((base-(te.target.to_numpy()-bp[k])**2)[jx])))
            zeros+=not ba['apply_correction'];max_change=max(max_change,ba['maximum_absolute_fixed_change']);arrays.append(np.stack([bp[k] for k in pp]))
        np.savez_compressed(out/f'{label}_refits.npz',predictions=np.asarray(arrays),model_names=np.asarray(list(pp)))
        result['temporal'][label]['full_refits']={'draws':refits,'zero_selection_count':zeros,'max_fixed_change':max_change,'comparisons':{k:{'absolute_gain_95':np.quantile(v,[.025,.975]).tolist() if v else None,'positive_fraction':float(np.mean(np.asarray(v)>0)) if v else None} for k,v in gains.items()},'scope':'Complete training-player resample/refit then paired test-player resample; 20-draw percentile tails are coarse descriptive sensitivity, not calibrated simultaneous coverage or independent confirmation.'}
        print(json.dumps({'stage':'temporal','label':label,'selected_gain':result['temporal'][label]['evaluation']['comparisons']['selected']['relative_gain']}),flush=True)
    # Conditional mislinking control preserves source-position/class strata.
    tr=dev[dev.draft_year.eq(2023)].reset_index(drop=True);te=dev[dev.draft_year.eq(2024)].reset_index(drop=True)
    rng=np.random.default_rng(3714);null=[];fractions=[]
    for b in range(permutations):
        shuffled=dev.copy();mapping=np.arange(len(dev))
        for _,g in dev.groupby(['draft_year','combine_position'],dropna=False):mapping[g.index]=rng.permutation(g.index)
        shuffled.loc[:,list(COLUMNS)]=dev.iloc[mapping][list(COLUMNS)].to_numpy()
        sp,_=fit_predict(shuffled[shuffled.draft_year.eq(2023)].reset_index(drop=True),shuffled[shuffled.draft_year.eq(2024)].reset_index(drop=True),1714)
        null.append(summary(te,sp)['comparisons']['selected']['absolute_gain']);fractions.append(float(np.mean(mapping!=np.arange(len(dev)))))
    result['mislinking_control']={'draws':permutations,'absolute_gains':null,'mean_reassigned_fraction':float(np.mean(fractions)) if fractions else None,'scope':'Class/source-position constrained mislinking sensitivity; not a formal p-value or new independent evidence.'}
    return result

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in ('players','events','private-out','aggregate'):p.add_argument('--'+key,type=Path,required=True)
    p.add_argument('--refits',type=int,default=20);p.add_argument('--permutations',type=int,default=16);a=p.parse_args()
    if a.refits<0 or a.permutations<0:p.error('nonnegative iteration counts required')
    if a.private_out.resolve()==ROOT or ROOT in a.private_out.resolve().parents:p.error('private outputs must stay outside checkout')
    start=time.perf_counter();r=run(pd.read_pickle(a.players),pd.read_pickle(a.events),a.private_out,a.refits,a.permutations)
    r['input_sha256']={k:sha(v) for k,v in [('players',a.players),('events',a.events)]};r['source_sha256']={str(v.relative_to(ROOT)):sha(v) for v in [ROOT/'python/perfectpower/combine_compact.py',Path(__file__),ROOT/'python/perfectpower/movement_residual.py']};r['versions']={'python':platform.python_version(),'numpy':np.__version__,'pandas':pd.__version__,'sklearn':sklearn.__version__};r['elapsed_seconds']=time.perf_counter()-start
    a.aggregate.parent.mkdir(parents=True,exist_ok=True);a.aggregate.write_text(json.dumps(r,indent=2,allow_nan=False)+'\n')
if __name__=='__main__':main()
