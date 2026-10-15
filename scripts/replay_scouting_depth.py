#!/usr/bin/env python3
"""Replay every selected endpoint on saved outer predictions with the final core.

This verifies selected fits, not independent validation or full tuning refits.
"""
import argparse,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np,pandas as pd
from perfectpower.scouting_depth import fit_predict,specs


def replay(players,predictions,extended_predictions):
    u=pd.read_pickle(players);records=[]
    cases=[('target','evaluation_target.json',predictions),('pressure_target','evaluation_pressure_target.json',predictions),('receiving_efficiency','evaluation_receiving_extended.json',extended_predictions)]
    for target,name,directory in cases:
        receipt=json.loads((ROOT/'receipts/scouting_depth'/name).read_text())[target];saved=pd.read_pickle(directory/(target+'_predictions.pkl'))
        rows=u[u[target].notna()].copy();rows['target']=rows[target];rows['log_pick']=np.log(rows.pick);features=specs(rows)
        for fold in receipt['outer_audits']:
            year=fold['class'];tr=rows[rows.draft_year.le(year-2)].reset_index(drop=True);te=rows[rows.draft_year.eq(year)].reset_index(drop=True);expected=saved[saved.draft_year.eq(year)].set_index('pfr_id').loc[te.pfr_id]
            for family,cols in features.items():
                actual=fit_predict(tr,te,cols,fold['configs'][family]['selected']);delta=float(np.max(np.abs(actual-expected[family].to_numpy())))
                if delta>1e-10:raise ValueError('selected-model replay differs '+target+' '+str(year)+' '+family+' '+str(delta))
                records.append({'target':target,'class':year,'family':family,'players':len(te),'max_abs_difference':delta})
            for prefix in ('','draft_'):
                cfg=fold['configs'][prefix+'optional'];endpoint=prefix+('custom' if cfg['accept_custom'] else 'raw')
                np.testing.assert_equal(expected[prefix+'optional'].to_numpy(),expected[endpoint].to_numpy())
    return {'schema':'pp-scouting-depth-prediction-replay/1','endpoint_fits':len(records),'maximum_abs_difference':max(x['max_abs_difference'] for x in records),'records':records,'zero_fallback_identity_verified':True,'full_inner_tuning_replayed':False,'scope':'All selected outer endpoint models replayed on the final expanded source population; saved fold configurations are reused, not selected again. Primary and pressure evaluation populations are unchanged.','core_sha256':hashlib.sha256((ROOT/'python/perfectpower/scouting_depth.py').read_bytes()).hexdigest()}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--players',type=Path,required=True);p.add_argument('--predictions',type=Path,required=True);p.add_argument('--extended-predictions',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();r=replay(a.players,a.predictions,a.extended_predictions);a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k!='records'}))
