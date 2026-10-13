"""Compile finite oscillator proofs and source-bound literal arithmetic fixtures."""
import hashlib,json,os,re,shutil,subprocess,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
import sys
sys.path.insert(0,str(ROOT/'python'))
from perfectpower.arithmetic_transport import height_ballot

def main():
    binary=os.environ.get('PERFECTPOWER_LEAN') or shutil.which('lean')
    if not binary:raise RuntimeError('Lean 4.20.0 is required; set PERFECTPOWER_LEAN')
    version=subprocess.check_output([binary,'--version'],text=True).strip()
    if not version.startswith('Lean (version 4.20.0,'):raise RuntimeError(version)
    source=ROOT/'PerfectPower/ArithmeticHeightPauli.lean';raw=source.read_text()
    if re.search(r'\b(sorry|native_decide|axiom)\b',re.sub(r'/\-.*?\-/','',raw,flags=re.S)):
        raise RuntimeError('Unproved or native assumptions are forbidden')
    names=re.findall(r'^theorem (\w+)',raw,re.M)
    generated=['namespace PerfectPower.ArithmeticHeightPauli.Fixtures']
    inputs=[]
    for p,q in ((2,3),(2,5),(3,5),(5,7)):
        for d in range(1,7):
            count=height_ballot(p,q,d)['count'];name=f'ballot_{p}_{q}_{d}'
            generated.append(f'theorem {name} : ballot {p} {q} {d} {d} = {count} := by simp only [ballot]; decide')
            inputs.append(dict(p=p,q=q,d=d,count=count,theorem=name))
    generated+=['end PerfectPower.ArithmeticHeightPauli.Fixtures']
    statements='\n'.join(generated)+'\n'
    audit=raw+'\n'+statements+'\n'+''.join(f'#print axioms PerfectPower.ArithmeticHeightPauli.{n}\n' for n in names)
    audit+=''.join(f'#print axioms PerfectPower.ArithmeticHeightPauli.Fixtures.{r["theorem"]}\n' for r in inputs)
    t=time.perf_counter()
    with tempfile.TemporaryDirectory() as tmp:
        path=Path(tmp)/'ArithmeticHeightPauliAudit.lean';path.write_text(audit)
        run=subprocess.run([binary,str(path)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    log=run.stdout+run.stderr
    if run.returncode or 'warning:' in log:raise RuntimeError(log)
    axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
    axioms += [(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    if len(axioms)!=len(names)+len(inputs):raise RuntimeError('Missing axiom records')
    for name,a in axioms:
        used=set(x.strip() for x in a.split(',') if x.strip())
        if not used<={'propext','Quot.sound','Classical.choice'}:raise RuntimeError((name,a))
    out=ROOT/'receipts/arithmetic_transport';out.mkdir(exist_ok=True,parents=True)
    (out/'kernel.log').write_text(log)
    (out/'literal_fixtures.lean').write_text('import PerfectPower.ArithmeticHeightPauli\n'+statements)
    receipt={'schema':'pp-arithmetic-transport-kernel/1','status':'passed','lean_version':version,
        'generic_theorems':len(names),'literal_theorems':len(inputs),'seconds':time.perf_counter()-t,
        'axioms':{n:[x.strip() for x in a.split(',') if x.strip()] for n,a in axioms},'fixtures':inputs,
        'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
            for p in (source,Path(__file__),ROOT/'python/perfectpower/arithmetic_transport.py')},
        'scope':'Generic finite coordinate walks, d-step root-edge support, complete distinct height-barrier word enumeration, actual integer height equivalence, shifted power preservation, Gaussian-integer Pauli charge identities, and 24 literal counts.',
        'open':'Prime factorization embedding, weighted matrix-power multiplicities, real/complex operator analysis, Python DP refinement, survival limit, and asymptotic correction are outside these Lean proofs.'}
    (out/'kernel.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ('status','generic_theorems','literal_theorems','seconds')}))

if __name__=='__main__':main()
