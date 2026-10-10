#!/usr/bin/env python3
"""Compile the BLAST bridge and literal model packets; save source-bound evidence."""
import argparse
from pathlib import Path
from hashlib import sha256
import subprocess
import os
import re
import json

ROOT=Path(__file__).resolve().parents[1]
MODULES=[('PerfectPower/SOESemantics.lean','lean_soe_semantics.log'),
         ('PerfectPower/BlastAlignment.lean','lean_scoring.log'),
         ('PerfectPower/Generated/BlastAlignmentSOE.lean','lean_alignment_soe.log'),
         ('PerfectPower/Generated/BlastMotifSOE.lean','lean_motif_soe.log'),
         ('PerfectPower/Generated/BlastPathCounts.lean','lean_path_counts.log'),
         ('PerfectPower/Generated/BlastScores.lean','lean_retained_scores.log')]


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--lean',help='explicit Lean executable; otherwise use lake env lean')
    args=parser.parse_args();command=[args.lean] if args.lean else ['lake','env','lean']
    env=dict(os.environ);build=ROOT/'.lake/build/lib/lean'
    if args.lean:env['LEAN_PATH']=str(build)+':'+env.get('LEAN_PATH','')
    version=subprocess.run(command+['--version'],cwd=ROOT,env=env,capture_output=True,text=True,check=True).stdout.strip()
    rows=[]
    for module,logname in MODULES:
        source=ROOT/module;target=build/Path(module).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
        result=subprocess.run(command+['-o',str(target),str(source.relative_to(ROOT))],cwd=ROOT,env=env,capture_output=True,text=True,timeout=600)
        output=result.stdout+result.stderr
        (ROOT/'receipts/blast'/logname).write_text(output)
        axiom_sets=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',output)
        axioms=sorted({name.strip() for group in axiom_sets for name in group.split(',') if name.strip()})
        accepted=result.returncode==0 and not re.search(r'\bsorryAx\b|error:|declaration uses .sorry.',output) and set(axioms)<={'propext','Classical.choice','Quot.sound'}
        rows.append({'module':module,'source_sha256':sha256(source.read_bytes()).hexdigest(),
            'accepted':accepted,'axioms':axioms,'log':logname,'returncode':result.returncode})
        print(module, 'accepted' if accepted else 'FAILED',flush=True)
        if not accepted:break
    receipt={'schema':'pp-blast-kernel-build/1','lean_version':version,'modules':rows,
             'accepted':len(rows)==len(MODULES) and all(r['accepted'] for r in rows),
             'scope':'listed generic scoring/path-length theorems and literal finite SOE/count/score packets; not Python DP correctness'}
    (ROOT/'receipts/blast/kernel_build.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    if not receipt['accepted']:raise SystemExit(1)


if __name__=='__main__':main()
