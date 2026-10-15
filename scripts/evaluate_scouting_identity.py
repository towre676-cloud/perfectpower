#!/usr/bin/env python3
"""One fixed delayed mathematical aggregation; no recruitment leakage."""
import argparse,hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
import numpy as np
import pandas as pd
from perfectpower.scouting_identity import EXPERTS,BOUNDS,delayed_aggregate
from run_scouting_depth import compare

def evaluate(paths,out,receipt):
    out.mkdir(parents=True,exist_ok=True);result={'schema':'pp-scouting-delayed-aggregation/1','retrospective_development':True,'untouched_confirmation':False,'eta':1.,'experts':EXPERTS,'protocol_sha256':hashlib.sha256((ROOT/'docs/SCOUTING_IDENTITY_PROTOCOL.json').read_bytes()).hexdigest(),'targets':{}}
    for target,path in zip(BOUNDS,paths):
        source=pd.read_pickle(path);bound=BOUNDS[target];q,weights=delayed_aggregate(source,bound)
        unclipped=q.target.copy();q['original_combine']=q['combine'];q['target']=np.clip(q.target,0,bound)
        clips={c:int(((source[c]<0)|(source[c]>bound)).sum()) for c in ['target',*EXPERTS]}
        for expert in EXPERTS:q[expert]=np.clip(q[expert],0,bound)
        pairs={f'aggregate_vs_{expert}':compare(q,'aggregate',expert) for expert in EXPERTS}
        # Clipping changes the theorem's estimand. Retain an original-target
        # sensitivity; never present the regret statement for unbounded labels.
        original=q.copy();original['target']=unclipped
        pairs['aggregate_vs_original_combine_original_target']=compare(original,'aggregate','original_combine')
        q['equal_average']=q[list(EXPERTS)].mean(axis=1)
        equal_diagnostic={'aggregate_vs_equal_average':compare(q,'aggregate','equal_average'),'max_prediction_change':float((q['aggregate']-q.equal_average).abs().max())}
        q.to_pickle(out/(target+'_aggregate.pkl'))
        class_losses={str(y):{'players':len(g),'aggregate':float(((g.target-g['aggregate'])/bound).pow(2).mean()),**{e:float(((g.target-g[e])/bound).pow(2).mean()) for e in EXPERTS}} for y,g in q.groupby('draft_year')}
        certificate={}
        for parity in (0,1):
            seq=[v for y,v in class_losses.items() if int(y)%2==parity];n=len(seq)
            if not n:continue
            actual=sum(v['aggregate'] for v in seq);best=min(sum(v[e] for v in seq) for e in EXPERTS)
            budget=float(np.log(len(EXPERTS))+n/8.)
            certificate[str(parity)]={'rounds':n,'normalized_equal_class_aggregate_loss':actual,'best_fixed_expert_loss':best,'regret':actual-best,'upper_bound':budget,'bound_satisfied':bool(actual-best<=budget+1e-12)}
        result['targets'][target]={'players':len(q),'bound':bound,'outcome_clipped':int(((unclipped<0)|(unclipped>bound)).sum()),'expert_clipped':clips,'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'comparisons':pairs,'weights':weights,'equal_average_diagnostic':equal_diagnostic,'class_normalized_losses':class_losses,'deterministic_regret_receipt':certificate}
        print(json.dumps({'target':target,'players':len(q),'gains':{k:v['relative_gain'] if 'relative_gain' in v else v for k,v in pairs.items()}}),flush=True)
    result['source_sha256']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(__file__),ROOT/'python/perfectpower/scouting_identity.py']}
    receipt.write_text(json.dumps(result,indent=2)+'\n');return result
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--predictions',type=Path,nargs=3,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True);a=p.parse_args();evaluate(a.predictions,a.out,a.receipt)
