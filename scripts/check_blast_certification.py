#!/usr/bin/env python3
"""Fresh kernel build; retain exact theorem sources, logs and axiom inventories."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import time
import sys

ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--lean',required=True);parser.add_argument('--jobs',type=int,default=2)
    args=parser.parse_args();out=ROOT/'receipts/blast/certification';build=ROOT/'.lake/build/lib/lean'
    env=dict(os.environ,LEAN_PATH=str(build)+':'+os.environ.get('LEAN_PATH',''))
    version=subprocess.run([args.lean,'--version'],capture_output=True,text=True,check=True,env=env).stdout.strip()
    manifest=json.loads((out/'source_kernel_inputs.json').read_text())
    sys.path.insert(0,str(ROOT/'python'))
    from generate_blast_source_certificates import validate_encoding
    validate_encoding(manifest)
    def compile(module):
        source=ROOT/module;target=build/Path(module).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        start=time.perf_counter()
        result=subprocess.run([args.lean,'-o',str(target),module],cwd=ROOT,env=env,capture_output=True,text=True,timeout=1800)
        text=result.stdout+result.stderr
        axioms=sorted({a.strip() for match in re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text) for a in match.split(',') if a.strip()})
        accepted=result.returncode==0 and not re.search(r'\bsorryAx\b|error:|declaration uses .sorry.',text) and set(axioms)<={'propext','Classical.choice','Quot.sound'}
        log=Path(module).stem+'.log';(out/log).write_text(text)
        row={'module':module,'source_sha256':sha256(source.read_bytes()).hexdigest(),'accepted':accepted,
             'axioms':axioms,'log':log,'elapsed_seconds':time.perf_counter()-start,'returncode':result.returncode}
        print(module,'accepted' if accepted else 'FAILED',flush=True)
        return row
    rows=[]
    for module in ['PerfectPower/BlastRecurrence.lean','PerfectPower/BlastSourceReplay.lean',manifest['modules'][0]]:
        row=compile(module);rows.append(row)
        if not row['accepted']:break
    if all(r['accepted'] for r in rows):
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            rows+=list(executor.map(compile,manifest['modules'][1:]))
    receipt={'schema':'pp-blast-certification-kernel/1','lean_version':version,'modules':rows,
             'accepted':len(rows)==len(manifest['modules'])+2 and all(r['accepted'] for r in rows),
             'literal_run_coverage':manifest['runs'],
             'source_encoding_rechecked':True,
             'scope':'general path coefficient recurrence, rank-bound completeness, generic BTOP decoder soundness, and listed literal run inputs; Python parser/DP and XML acquisition are not kernel-proved'}
    (out/'kernel_build.json').write_text(json.dumps(receipt,indent=2)+'\n')
    if not receipt['accepted']:raise SystemExit(1)


if __name__=='__main__':main()
