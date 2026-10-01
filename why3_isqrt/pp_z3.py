"""Why3-compatible prover wrapper; ground arithmetic certificates only.

Configure Why3's prover command as:
python /absolute/pp_z3.py --solver /absolute/z3 --seconds %t %f
Use the z3_487 driver for native bitvectors. Ordinary Z3 output is preserved.
"""
import argparse,json,pathlib,subprocess,sys,time
import sys as _sys
_sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "python"))
from perfectpower.unsigned_adapter import accelerate,check,digest

def main():
    p=argparse.ArgumentParser();p.add_argument('task');p.add_argument('--solver',default='z3')
    p.add_argument('--seconds',type=int,default=3);p.add_argument('--policy',choices=['goal','all'],default='goal')
    p.add_argument('--receipts');a=p.parse_args()
    text=pathlib.Path(a.task).read_text();start=time.perf_counter();reason=None
    try:out,cert=accelerate(text,policy=a.policy)
    except (ValueError,Exception) as e:
        # Fail open for acceleration: replay the intact original task in Z3.
        out=text;cert=None;reason=type(e).__name__
    prep=time.perf_counter()-start
    try:
        run=subprocess.run([a.solver,'-in','-smt2','-T:'+str(max(1,a.seconds))],
                           input=out,capture_output=True,text=True,timeout=max(1,a.seconds)+2)
        sys.stdout.write(run.stdout);sys.stderr.write(run.stderr);code=run.returncode
    except subprocess.TimeoutExpired:
        sys.stdout.write('timeout\n');code=0
    if a.receipts:
        root=pathlib.Path(a.receipts);root.mkdir(parents=True,exist_ok=True)
        row=dict(task_sha256=digest(text),policy=a.policy,prepare_seconds=prep,
                 total_seconds=time.perf_counter()-start,certificate=cert,fallback=reason)
        (root/(digest(text)+'.json')).write_text(json.dumps(row,indent=2)+'\n')
    return code

if __name__=='__main__':raise SystemExit(main())
