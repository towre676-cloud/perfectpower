"""Compile and audit the literal protected compatibility transport, Std only."""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT=Path(__file__).resolve().parents[1]


def main():
    binary=os.environ.get('PERFECTPOWER_LEAN') or shutil.which('lean')
    if not binary:raise RuntimeError('Lean 4.20.0 required')
    version=subprocess.check_output([binary,'--version'],text=True).strip()
    assert version.startswith('Lean (version 4.20.0,')
    example=json.loads((ROOT/'examples/planning/compatible_slots.json').read_text())['specification']
    expected={'model':{'observations':[0]*4,'actions':{'skip':[0,1,2,3],'take':[1,0,3,2]}},'initial':0,'accepting':[0,2]}
    assert example['machine']==expected
    assert all(v['upper']==1 and v['actions']=={'0':'skip','1':'take'} for v in example['variables'])
    path='PerfectPower/PlannerTransport.lean'
    run=subprocess.run([binary,path],cwd=ROOT,capture_output=True,text=True,timeout=120)
    log=run.stdout+run.stderr
    assert run.returncode==0 and 'sorry' not in log and 'warning:' not in log,log
    rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
    expected_names=['run_transport','transition_preserved','all_words','same_plans','same_count','same_scores']
    assert [n for n,a in rows]==['PerfectPower.PlannerTransport.'+n for n in expected_names]
    for name,axioms in rows:assert set(map(str.strip,axioms.split(','))) <= {'propext','Quot.sound','Classical.choice'}
    out=ROOT/'receipts/planning';out.mkdir(parents=True,exist_ok=True)
    (out/'PlannerTransport.log').write_text(log)
    receipt={'schema':'pp-planning-kernel/1','status':'passed','lean_version':version,'declarations':len(rows),
             'axioms':{n:list(map(str.strip,a.split(','))) for n,a in rows},
             'source_sha256':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in [path,'scripts/check_planning_kernel.py','examples/planning/compatible_slots.json']},
             'scope':'all finite Boolean action words and candidate menus for the literal four-to-two-state protected machine; same ordered plans, counts and arbitrary score lists',
             'open':'Python planner/parser/fold/routing refinement and arbitrary generated SOE acceptance are not established by this audit'}
    (out/'kernel.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'passed','declarations':len(rows)}))


if __name__=='__main__':main()
