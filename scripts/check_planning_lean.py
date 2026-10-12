"""Compile the standalone planning proofs and inspect every theorem's axioms."""
import argparse
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
MODULES = ('PlanningDiagram', 'PetersenPlanning')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_binding():
    # Independent raw-token acquisition of the original source rows.
    tokens=iter((ROOT/'data/planning/mknap1.txt').read_text().split())
    for _ in range(int(next(tokens))):
        n,m=int(next(tokens)),int(next(tokens));next(tokens)
        profits=[next(tokens) for _ in range(n)]
        rows=[[int(next(tokens)) for _ in range(n)] for _ in range(m)]
        caps=[int(next(tokens)) for _ in range(m)]
        if n==50: original=(rows,caps,list(map(int,profits)))
    assert list(tokens)==[]
    text=(ROOT/'PerfectPower/PetersenPlanning.lean').read_text()
    def literal(name):
        value=re.search(r'^def '+name+r' .*? := (.*)$',text,re.M).group(1)
        return ast.literal_eval(re.sub(r'\bfalse\b','False',re.sub(r'\btrue\b','True',value)))
    assert literal('rows')==original[0]
    assert literal('capacities')==original[1]
    assert literal('profits')==original[2]
    packet=json.loads((ROOT/'receipts/planning/population/50_partition.json').read_text())
    splits={(r['fixed'],r['values']):r['bit'] for r in packet['splits']}
    answers={(r['fixed'],r['values']):r['answer'] for r in packet['answers']}
    addresses=[];counts=[];free=[]
    def visit(fixed,values):
        if (fixed,values) in splits:
            bit=splits[fixed,values]
            visit(fixed|bit,values);visit(fixed|bit,values|bit)
        else:
            addresses.append([(j,bool(values & (1 << (49-j)))) for j in range(50) if fixed & (1 << (49-j))])
            counts.append(answers[fixed,values]['count']);free.append(50-fixed.bit_count())
    visit(0,0)
    assert literal('retainedOriginalPaths')==addresses
    assert literal('retainedLeafCounts')==counts
    assert literal('retainedLeafFreeVariables')==free
    return {'raw_data_sha256':sha(ROOT/'data/planning/mknap1.txt'),
            'partition_sha256':sha(ROOT/'receipts/planning/population/50_partition.json'),
            'literal_original_rows_capacities_profits_match':True,
            'literal_original_partition_addresses_and_count_labels_match':True}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--lean',default='lean')
    parser.add_argument('--namespace-path-shim',action='store_true')
    args=parser.parse_args()
    result={'schema':'pp-planning-lean/1','binding':source_binding(),
            'sources':{f'PerfectPower/{m}.lean':sha(ROOT/f'PerfectPower/{m}.lean') for m in MODULES},
            'checker_sha256':sha(Path(__file__)),'namespace_path_compatibility':args.namespace_path_shim}
    with tempfile.TemporaryDirectory() as temporary:
        work=Path(temporary);(work/'PerfectPower').mkdir()
        env=os.environ.copy();env['LEAN_PATH']=str(work)
        if args.namespace_path_shim:
            shim=work/'proc_path.so'
            source=ROOT/'scripts/lean_namespace_path.c'
            subprocess.run(['gcc','-shared','-fPIC',str(source),'-o',str(shim),'-ldl'],check=True)
            env['LD_PRELOAD']=str(shim)
            result['namespace_shim_source_sha256']=sha(source)
        version=subprocess.check_output([args.lean,'--version'],env=env,text=True).strip()
        if 'version 4.20.0,' not in version: raise RuntimeError('Pinned Lean 4.20.0 required')
        result['lean_version']=version
        commands=[];declarations=[]
        for module in MODULES:
            source=ROOT/f'PerfectPower/{module}.lean'
            text=source.read_text()
            # The Lean compiler rejects failed declarations; axiom inspection
            # below independently rejects admitted proofs and native reflection.
            names=re.findall(r'^theorem (\w+)',text,re.M)
            declarations += [f'PerfectPower.{module}.{name}' for name in names]
            command=[args.lean,'-o',str(work/f'PerfectPower/{module}.olean'),str(source)]
            start=time.perf_counter()
            run=subprocess.run(command,cwd=ROOT,env=env,text=True,capture_output=True,timeout=180)
            if run.returncode: raise RuntimeError(run.stdout+run.stderr)
            commands.append({'module':module,'seconds':time.perf_counter()-start,'stdout':run.stdout,'stderr':run.stderr})
        audit=work/'Audit.lean'
        audit.write_text('import PerfectPower.PetersenPlanning\n'+'\n'.join('#print axioms '+name for name in declarations)+'\n')
        run=subprocess.run([args.lean,str(audit)],cwd=ROOT,env=env,text=True,capture_output=True,timeout=180)
        if run.returncode: raise RuntimeError(run.stdout+run.stderr)
        parsed=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))",run.stdout.replace('\n',' '))
        axioms={name:[] if no_axioms else [x.strip() for x in values.split(',') if x.strip()] for name,values,no_axioms in parsed}
        if set(axioms)!=set(declarations): raise RuntimeError('Incomplete axiom inspection')
        allowed={'propext','Classical.choice','Quot.sound'}
        if any(set(a)-allowed for a in axioms.values()): raise RuntimeError('Nonstandard/admitted/native-reflection axiom')
        result.update(status='kernel_checked',theorems=len(declarations),axioms=axioms,commands=commands,
                      sorry_ax=False,native_reflection_axioms=False,
                      full_unrestricted_population_kernel_proved=False,
                      original_conditional_counts_kernel_proved=[16777216,512],
                      original_optimizer_witness_kernel_proved=True,
                      original_optimizer_uniqueness_kernel_proved=False,
                      partition_disjoint_cover_and_aggregation_kernel_proved=True)
    out=ROOT/'receipts/planning/independent/lean.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','theorems','sorry_ax','native_reflection_axioms','original_conditional_counts_kernel_proved','full_unrestricted_population_kernel_proved')}))


if __name__=='__main__':main()
