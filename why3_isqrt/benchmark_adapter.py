"""Paired replay of original host-emitted VCs and guarded lemma injection."""
import argparse,json,pathlib,subprocess,time
import sys as _sys
_sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "python"))
from perfectpower.unsigned_adapter import accelerate,check

def solve(z3,task,budget,seed):
    start=time.perf_counter()
    try:
        p=subprocess.run([z3,'-in','-smt2','-T:'+str(budget),'smt.random_seed='+str(seed)],
                         input=task,capture_output=True,text=True,timeout=budget+2)
        status=next((s for s in p.stdout.splitlines() if s in ('unsat','sat','unknown','timeout')),'error')
    except subprocess.TimeoutExpired:status='timeout'
    return dict(status=status,seconds=time.perf_counter()-start)

def run(root,z3,budget,seeds,hard_only=False,policy='goal'):
    baseline=json.loads((root/'receipts'/'bv_baseline.json').read_text())
    hard={r['file'] for r in baseline if r['status']!='unsat'}
    rows=[]
    for p in sorted((root/'raw_bv_vcs').glob('*.smt2')):
        if hard_only and p.name not in hard:continue
        text=p.read_text();t=time.perf_counter();out,cert=accelerate(text,policy=policy)
        elapsed=time.perf_counter()-t
        if cert['steps']:assert check(text,cert)
        for seed in seeds:
            # Alternate arm order to reduce systematic timing bias.
            if seed%2:
                accelerated=solve(z3,out,budget,seed);original=solve(z3,text,budget,seed)
            else:
                original=solve(z3,text,budget,seed);accelerated=solve(z3,out,budget,seed)
            accelerated['total_seconds']=accelerated['seconds']+elapsed
            row=dict(file=p.name,seed=seed,steps=len(cert['steps']),prepare_seconds=elapsed,
                     original=original,accelerated=accelerated)
            rows.append(row)
            print(p.name,seed,original['status'],accelerated['status'],
                  round(original['seconds'],4),round(accelerated['total_seconds'],4),flush=True)
        (root/'certificates').mkdir(exist_ok=True)
        (root/'certificates'/(p.stem+'.json')).write_text(json.dumps(cert,indent=2)+'\n')
    name=f'paired_{policy}_'+('hard.json' if hard_only else 'all.json')
    (root/'receipts'/name).write_text(json.dumps(dict(policy=policy,budget_seconds=budget,z3_version=subprocess.run(
        [z3,'--version'],capture_output=True,text=True).stdout.strip(),rows=rows),indent=2)+'\n')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--z3',default='z3');ap.add_argument('--budget',type=int,default=3)
    ap.add_argument('--seeds',default='0');ap.add_argument('--hard-only',action='store_true')
    ap.add_argument('--policy',choices=['goal','all'],default='goal')
    a=ap.parse_args();run(pathlib.Path(__file__).resolve().parent,a.z3,a.budget,
                        [int(s) for s in a.seeds.split(',')],a.hard_only,a.policy)
