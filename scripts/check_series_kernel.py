"""Compile current series foundations, source-bound packets and every named proof."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from perfectpower.telescoping import export_lean_binomial
BASE=['PerfectPower/GeneratingFunctions.lean','PerfectPower/CertifiedTelescoping.lean',
      'PerfectPower/CertifiedBinary64.lean','PerfectPower/CertifiedSeriesBounds.lean',
      'PerfectPower/CertifiedRealization.lean']
GENERATED=[f'PerfectPower/Generated/BinomialPower{p}.lean' for p in range(1,5)]
OUT=ROOT/'receipts/series_kernel'
ALLOWED={'propext','Classical.choice','Quot.sound'}


def digest(path):return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()

def names(path):
    stack=[];out=[]
    for line in (ROOT/path).read_text().splitlines():
        match=re.match(r'^namespace (\S+)',line)
        if match:stack.append(match.group(1))
        match=re.match(r'^(?:theorem|lemma) (\w+)',line)
        if match:out.append('.'.join(stack+[match.group(1)]))
        if re.match(r'^end\b',line) and stack:stack.pop()
    return out

def run(path,output=None):
    cmd=[os.environ.get('PERFECTPOWER_LAKE','lake'),'env',os.environ.get('PERFECTPOWER_LEAN','lean'),path]
    if output:cmd+=['-o',str(output)]
    result=subprocess.run(cmd,cwd=ROOT,text=True,capture_output=True)
    log=result.stdout+result.stderr
    (OUT/(Path(path).stem+'.log')).write_text(log)
    if result.returncode or re.search(r'\b(?:error|warning):',log):raise RuntimeError(path+'\n'+log)
    return log

def main():
    OUT.mkdir(exist_ok=True)
    version=subprocess.run([os.environ.get("PERFECTPOWER_LAKE","lake"),"env",os.environ.get("PERFECTPOWER_LEAN","lean"),"--version"],cwd=ROOT,text=True,capture_output=True,check=True).stdout.strip()
    assert version.startswith("Lean (version 4.20.0,"),version
    for p,path in enumerate(GENERATED,1):
        packet=json.loads((ROOT/f'receipts/telescoping/binomial_power_{p}.json').read_text())['definition']
        expected=export_lean_binomial(packet,f'PerfectPower.Generated.BinomialPower{p}')
        assert (ROOT/path).read_text()==expected,'retained Lean packet differs from current source'
    modules=BASE+GENERATED
    declarations=[name for path in modules for name in names(path)]
    assert len(declarations)==len(set(declarations))
    audit='\n'.join('import '+path.removesuffix('.lean').replace('/','.') for path in modules)+'\n\n'
    audit+='\n'.join('#print axioms '+name for name in declarations)+'\n'
    assert (ROOT/'audit/SeriesKernel.lean').read_text()==audit,'audit omits or changes a declaration'
    for i,path in enumerate(modules):
        dest=ROOT/'.lake/build/lib/lean'/Path(path).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        run(path,dest)
        print(f'kernel checked {i+1}/{len(modules)}: {path}',flush=True)
    log=run('audit/SeriesKernel.lean')
    pattern=re.compile(r"'([^']+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])")
    records=[]
    for match in pattern.finditer(log):
        axioms=[a.strip() for a in (match.group(2) or '').split(',') if a.strip()]
        assert not set(axioms)-ALLOWED,(match.group(1),axioms)
        records.append({'name':match.group(1),'axioms':axioms})
    assert [row['name'] for row in records]==declarations
    assert not pattern.sub('',log).strip(),'unexpected audit output'
    sources=modules+['audit/SeriesKernel.lean','scripts/check_series_kernel.py','python/perfectpower/telescoping.py']
    sources += [f'receipts/telescoping/binomial_power_{p}.json' for p in range(1,5)]
    receipt={'schema':'pp-series-kernel/1','status':'passed','lean_version':'4.20.0',
        'runtime_version':version,'declaration_count':len(records),'declarations':records,'source_sha256':{path:digest(path) for path in sources},
        'log_sha256':{path.relative_to(ROOT).as_posix():hashlib.sha256(path.read_bytes()).hexdigest() for path in sorted(OUT.glob('*.log'))},
        'scope':'the listed mathematical foundations and source-bound binomial recurrence packets; not a complete historical root build or full Python implementation refinement'}
    (OUT/'validation.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':'passed','declarations':len(records)}))
if __name__=='__main__':main()
