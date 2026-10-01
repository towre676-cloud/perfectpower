"""Replay unchanged Why3-produced SMT tasks. No certificate or added premise."""
import argparse, hashlib, json, pathlib, subprocess, time

def run(root, z3, timeout=3):
    rows=[]
    for p in sorted((root/'raw_vcs').glob('*.smt2')):
        start=time.perf_counter()
        try:
            proc=subprocess.run([z3, '-T:'+str(timeout), str(p)],capture_output=True,text=True,timeout=timeout+2)
            output=proc.stdout.strip()
            status=next((l for l in output.splitlines() if l in ('sat','unsat','unknown','timeout')), 'error')
        except subprocess.TimeoutExpired:
            status,output='timeout','process deadline'
        rows.append(dict(file=p.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),status=status,
                         seconds=time.perf_counter()-start,output=output))
        print(p.name,status,round(rows[-1]['seconds'],4),flush=True)
    (root/'receipts').mkdir(exist_ok=True)
    (root/'receipts'/'raw_baseline.json').write_text(json.dumps(rows,indent=2)+'\n')
    return rows

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--z3',default='z3');ap.add_argument('--timeout',type=int,default=3)
    a=ap.parse_args();run(pathlib.Path(__file__).resolve().parent,a.z3,a.timeout)
