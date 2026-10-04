"""Resume kernel checking any case interval, using bounded-size batches.

Example: python scripts/check_divisor_sum_catalogue.py --start-case 200 --stop-case 250
The default checks the full catalogue. Every successful batch is checkpointed.
"""
import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path
from time import perf_counter

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--start-case',type=int,default=0)
parser.add_argument('--stop-case',type=int)
parser.add_argument('--batch-size',type=int,default=10)
args=parser.parse_args()
root=Path(__file__).resolve().parents[1];out=root/'receipts/divisor_sum'
source=out/'CompleteQuartics.lean';lines=source.read_text().splitlines()
header,body,footer=lines[:5],lines[5:-1],lines[-1]
if len(body)%2:raise SystemExit('expected one command and packet theorem per case')
total=len(body)//2;stop=total if args.stop_case is None else args.stop_case
if not 0<=args.start_case<stop<=total or not 1<=args.batch_size<=100:
    raise SystemExit('invalid case interval or batch size')
source_hash=hashlib.sha256(source.read_bytes()).hexdigest()
validation_file=out/'lean_catalogue_validation.json'
validation=json.loads(validation_file.read_text()) if validation_file.exists() else {}
if validation.get('source_sha256')!=source_hash:validation={}
checked=set(validation.get('checked_case_indices',[]));logs=validation.get('logs',[])
start=perf_counter()
log=out/f'lean_cases_{args.start_case:05d}_{stop:05d}.log'
with tempfile.TemporaryDirectory(prefix='pp-sigma-lean-') as temp,log.open('w') as handle:
    for begin in range(args.start_case,stop,args.batch_size):
        end=min(begin+args.batch_size,stop)
        reports=[f'#print axioms curve_{i:04d}_{suffix}' for i in range(begin,end)
                 for suffix in ('complete','packet')]
        path=Path(temp)/'Cases.lean';path.write_text('\n'.join(header+body[2*begin:2*end]+reports+[footer])+'\n')
        result=subprocess.run(['lake','env','lean','-s','65536',str(path)],cwd=root,
                              text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        handle.write(result.stdout);handle.flush()
        if result.returncode:raise SystemExit(f'Lean failed at case {begin}; see {log}')
        groups=re.findall(r'depends on axioms: \[([^\]]*)\]',result.stdout)
        if len(groups)!=2*(end-begin):raise SystemExit('missing theorem reports')
        for group in groups:
            if {x.strip() for x in group.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'}:
                raise SystemExit('unexpected axiom')
        checked.update(range(begin,end))
        validation={'source_sha256':source_hash,'catalogue_equations':total,
            'compiled_complete_lists':len(checked),'compiled_packet_equalities':len(checked),
            'checked_case_indices':sorted(checked),'axiom_reports':2*len(checked),
            'status':'COMPLETE_KERNEL_CHECK' if len(checked)==total else 'PARTIAL_KERNEL_CHECK',
            'logs':sorted(set(logs+[log.name])),
            'lean_version':subprocess.check_output(['lean','--version'],text=True).strip(),
            'python_execution_verified':False,
            'scope':'only listed indices have kernel-checked literal point lists; other lists use proved family bounds and Python enumeration'}
        validation_file.write_text(json.dumps(validation,indent=2)+'\n')
        print(f'Cases {begin} through {end-1}: {len(checked)}/{total} complete lists and packet equalities checked',flush=True)
print(f'Finished requested interval in {perf_counter()-start:.2f}s',flush=True)
