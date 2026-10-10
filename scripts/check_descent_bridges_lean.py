"""Rebuild arithmetic descent bridges and reject nonstandard proof axioms."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
BASE=['PerfectPower/TwoDescentBridges.lean','PerfectPower/LocalQuarticBridges.lean',
 'PerfectPower/IsogenyCoordinates.lean','PerfectPower/IsogenyIndexBridges.lean']
INPUTS=['receipts/structural_math/two_isogeny_corpus.json','python/develop_descent_bridges_lean.py',
 'PerfectPower/StructuralCertificates.lean']
OUT=ROOT/'receipts/descent_bridges'
def digest(p):return hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
def configuration():
 manifest=json.loads((OUT/'instances.json').read_text())
 modules=BASE+manifest['modules'];names=[]
 for path in modules:
  source=(ROOT/path).read_text();ns=re.search(r'^namespace (\S+)',source,re.M).group(1)
  names.extend(ns+'.'+n for n in re.findall(r'^theorem (\w+)',source,re.M))
 assert len(names)==len(set(names))
 audit='\n'.join('import '+p.removesuffix('.lean').replace('/','.') for p in modules)+'\n'
 audit+='\n'.join('#print axioms '+n for n in names)+'\n'
 return manifest,modules,names,audit

def main():
 manifest,modules,names,audit=configuration()
 generated=manifest['modules']+['receipts/descent_bridges/instances.json']
 before={p:digest(p) for p in generated}
 subprocess.run(['python3','python/develop_descent_bridges_lean.py'],cwd=ROOT,check=True)
 assert before=={p:digest(p) for p in generated},'non-deterministic retained corpus generation'
 assert (ROOT/'audit/DescentBridges.lean').read_text()==audit,'incomplete declaration audit'
 OUT.mkdir(exist_ok=True)
 for i,path in enumerate(modules):
  dest=ROOT/'.lake/build/lib/lean'/Path(path).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  run=subprocess.run(['lake','env','lean','-o',str(dest),path],cwd=ROOT,text=True,capture_output=True)
  (OUT/(Path(path).stem+'.log')).write_text(run.stdout+run.stderr)
  if run.returncode or run.stdout.strip() or run.stderr.strip():raise RuntimeError(path+'\n'+run.stdout+run.stderr)
  print(f'compiled {i+1}/{len(modules)}: {path}',flush=True)
 run=subprocess.run(['lake','env','lean','audit/DescentBridges.lean'],cwd=ROOT,text=True,capture_output=True,check=True)
 pattern=re.compile(r"'([^']+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])")
 records=list(pattern.finditer(run.stdout))
 assert [m.group(1) for m in records]==names and not pattern.sub('',run.stdout).strip() and not run.stderr.strip(),'incomplete/unparsed audit'
 parsed=[]
 for m in records:
  axioms=[a.strip() for a in (m.group(2) or '').split(',') if a.strip()]
  assert not set(axioms)-{'propext','Quot.sound','Classical.choice'},(m.group(1),axioms)
  parsed.append(dict(declaration=m.group(1),axioms=axioms))
 (OUT/'axioms.log').write_text(run.stdout)
 receipt=dict(schema='pp-descent-bridges-lean/1',compiled=True,lean_version='4.20.0',
  declaration_count=len(parsed),declarations=parsed,excluded_covers=len(manifest['covers']),
  rational_models=len(manifest['models']),source_sha256={p:digest(p) for p in modules+INPUTS+[
   'receipts/descent_bridges/instances.json','audit/DescentBridges.lean','scripts/check_descent_bridges_lean.py']},
  scope='complete rational point-to-primitive-cover arithmetic and retained squareclass exclusions; isogeny coordinate identities and conditional group-index theorem; no unconditional elliptic rank theorem')
 (OUT/'verification.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:receipt[k] for k in ('compiled','declaration_count','excluded_covers','rational_models')}),flush=True)
if __name__=='__main__':main()
