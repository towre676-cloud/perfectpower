#!/usr/bin/env python3
"""Source support, complete-refit diagnostics and unchanged legacy metric replay."""
import argparse,hashlib,importlib.util,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd
from perfectpower.movement_residual import families,repeat_reliability
# Historical NFL-position specification is replayed only from its pinned source.
LEGACY=ROOT/'research/movement_language/run_movement_transfer_legacy.py'
if hashlib.sha256(LEGACY.read_bytes()).hexdigest()!='785673482be4626edcf338334c740baf57004000bf585cb75387b7da92b03469':raise ValueError('legacy replay source changed')
spec=importlib.util.spec_from_file_location('pp_movement_legacy_replay',LEGACY)
legacy_module=importlib.util.module_from_spec(spec);spec.loader.exec_module(legacy_module)
evaluate=legacy_module.evaluate


def audit(unit,events,private,aggregate):
    aggregate.mkdir(parents=True,exist_ok=True);dev=unit[unit.draft_year.isin([2023,2024])].reset_index(drop=True)
    cols=families(unit)['combined'];w,s=repeat_reliability(events,set(dev.nfl_id),cols)
    source={'schema':'pp-movement-residual-source-diagnostics/1','training_classes':[2023,2024],'calibration_scope':'Repeated source attempts, not labeled phases or physiological probability calibration. No NFL labels used. Reliability uses distinct training players even during player bootstrap.','drills':{}}
    for drill,g in events.groupby('drill_name'):
        counts=g.groupby('nfl_id').size();ix=[j for j,c in enumerate(cols) if c.split('__')[1]==drill]
        source['drills'][drill]={'all_class_attempts':len(g),'all_class_players':len(counts),'all_class_repeat_players':int((counts>1).sum()),'development_repeat_support':s[drill],'development_feature_reliability_quantiles':np.quantile(w[ix],[0,.25,.5,.75,1]).tolist(),'development_zero_weight_features':int((w[ix]==0).sum()),'features':len(ix)}
    source.update(exposure_quantiles=np.quantile(unit.exposure,[0,.1,.5,.9,1]).tolist(),sum_exposure=int(unit.exposure.sum()),no_phase_annotation_calibration=True)
    (aggregate/'residual_source_diagnostics.json').write_text(json.dumps(source,indent=2)+'\n')
    r=json.loads((aggregate/'residual.json').read_text());refits={'schema':'pp-movement-residual-refit-diagnostics/1','scope':'Fixed observed evaluation players for per-refit diagnostics; training bootstrap refitted all model steps. Not new-cohort evidence.','comparisons':{}}
    for label,tr,year in [('2023_to_2024',dev[dev.draft_year.eq(2023)].reset_index(drop=True),2024),('exploratory_2025',dev,2025)]:
        te=unit[unit.draft_year.eq(year)].reset_index(drop=True);pred=np.load(private/(label+'_refits.npz'))['predictions'];y=te.target.to_numpy();lb=(pred[:,0]-y)**2;lc=(pred[:,1]-y)**2;gain=(lb-lc).mean(axis=1);rng=np.random.default_rng(2714);resampled=[]
        if len(pred)<1:raise ValueError('full-refit diagnostic needs refits')
        for b in range(len(pred)):
            for _,g in tr.groupby('draft_year'):rng.choice(g.index,len(g),replace=True)
            ix=np.concatenate([rng.choice(g.index,len(g),replace=True) for _,g in te.groupby('draft_year')]);resampled.append(float((lb[b]-lc[b])[ix].mean()))
        delta=float(np.max(np.abs(np.quantile(resampled,[.025,.975])-r['temporal'][label]['full_refit_bootstrap']['absolute_gain_95'])))
        if delta>1e-15:raise ValueError('bootstrap replay mismatch')
        refits['comparisons'][label]={'refits':len(pred),'baseline_mse_quantiles':np.quantile(lb.mean(axis=1),[0,.025,.5,.975,1]).tolist(),'candidate_mse_quantiles':np.quantile(lc.mean(axis=1),[0,.025,.5,.975,1]).tolist(),'fixed_test_gain_quantiles':np.quantile(gain,[0,.025,.5,.975,1]).tolist(),'loss_over_10_percent_count':int((lc.mean(axis=1)>1.1*lb.mean(axis=1)).sum()),'gain_over_10_percent_count':int((lc.mean(axis=1)<.9*lb.mean(axis=1)).sum()),'largest_absolute_rate_correction':float(np.abs(pred[:,1]-pred[:,0]).max()),'postclip_boundary_prediction_count':int(((pred[:,1]==0)|(pred[:,1]==1)).sum()),'bootstrap_quantile_replay_max_difference':delta,'per_refit_aggregate_mse':{'conventional':lb.mean(axis=1).tolist(),'selected':lc.mean(axis=1).tolist()}}
    (aggregate/'residual_refit_diagnostics.json').write_text(json.dumps(refits,indent=2)+'\n')
    legacy=private/'legacy_replay';legacy.mkdir(exist_ok=True);new=evaluate(unit,legacy);old=json.loads((ROOT/'receipts/movement_language/transfer.json').read_text());diff=[]
    for split in ('nested_2023_2024','exploratory_2025'):
        for family in old[split]:
            for metric in ('baseline_mse','candidate_mse','relative_gain','absolute_gain'):diff.append(abs(new[split][family][metric]-old[split][family][metric]))
    result={'scalar_metrics':len(diff),'max_absolute_difference':max(diff)}
    (aggregate/'residual_legacy_audit.json').write_text(json.dumps(result,indent=2)+'\n');return result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--players',type=Path,required=True);p.add_argument('--events',type=Path,required=True);p.add_argument('--private-out',type=Path,required=True);p.add_argument('--aggregate-dir',type=Path,required=True);a=p.parse_args()
    if ROOT==a.private_out.resolve() or ROOT in a.private_out.resolve().parents:p.error('private output must be outside repository')
    print(json.dumps(audit(pd.read_pickle(a.players),pd.read_pickle(a.events),a.private_out,a.aggregate_dir)))
if __name__=='__main__':main()
