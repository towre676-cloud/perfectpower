"""Isolated Linux process peak RSS for selected hybrid workflows."""
import argparse
import json
import platform
import subprocess
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def worker(variant):
    import resource
    from run_planning import parse_public,bank,GrayIndex,ortools_optimum
    from run_planning_hybrid import native_exhaustive
    from perfectpower.planning import CompletionPlanner,optimize_allocation
    rows=parse_public()
    if variant=='mitm_20':answer=bank(CompletionPlanner(dict(rows[3]['specification'],strategy='mitm')))
    elif variant=='native_exhaustive_20':answer=bank(native_exhaustive(rows[3]['specification']))
    elif variant=='python_gray_20':answer=bank(GrayIndex(rows[3]['specification']))
    elif variant=='native_optimization_50':answer=optimize_allocation(rows[-1]['specification'])
    elif variant=='ortools_optimization_50':answer=ortools_optimum(rows[-1]['specification'])
    else:raise ValueError('unknown worker variant')
    assert answer.get('count',422601)==422601
    if variant.endswith('_50'):assert answer['maximum']=='16537' and answer['optimal']
    return {'variant':variant,'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024}

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--worker');a=p.parse_args()
    if a.worker:print(json.dumps(worker(a.worker)))
    else:
        out={'schema':'pp-planning-hybrid-memory/1','platform':platform.platform(),'scope':'fresh process per variant; includes interpreter, imports, index construction and full five-query bank or optimization-only search; compiler children excluded','variants':[]}
        if platform.system()!='Linux':out['status']='unavailable: Linux ru_maxrss convention required'
        else:
            for variant in ('mitm_20','native_exhaustive_20','python_gray_20','native_optimization_50','ortools_optimization_50'):
                r=subprocess.run([sys.executable,__file__,'--worker',variant],check=True,capture_output=True,text=True)
                value=json.loads(r.stdout);out['variants'].append(value);print(json.dumps(value),flush=True)
            out['status']='complete'
        target=ROOT/'receipts/planning/hybrid/memory.json';target.parent.mkdir(parents=True,exist_ok=True);target.write_text(json.dumps(out,indent=2)+'\n')
