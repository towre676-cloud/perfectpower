"""Compile the recovered new-work library and retain exact standard-axiom evidence."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
MODULES=['PerfectPower/PSGStructural.lean','PerfectPower/Generated/PSGStructuralPackets.lean',
 'PerfectPower/SOESemantics.lean','PerfectPower/StructuralCertificates.lean',
 'PerfectPower/StructuralSpecies.lean','PerfectPower/NewWorkClosure.lean',
 'PerfectPower/AdaptiveDiagnosis.lean','PerfectPower/Generated/StructuralPackets.lean',
 'PerfectPower/Generated/SOEModelPackets.lean']
INPUTS=['receipts/soe_bridge/all_two_state_automata.json','receipts/soe_bridge/adaptive_diagnosis.json',
 'receipts/structural_math/matrix_certificates.json','receipts/structural_math/psg_invariant_energy.json',
 'python/develop_new_work_lean.py','python/develop_psg_structural.py']

def digest(path):return hashlib.sha256((ROOT/path).read_bytes()).hexdigest()
def main():
 names=[]
 for path in MODULES:
  text=(ROOT/path).read_text();ns=re.search(r'^namespace (\S+)',text,re.M).group(1)
  names.extend(ns+'.'+m for m in re.findall(r'^theorem (\w+)',text,re.M))
 assert len(names)==len(set(names))
 generated=MODULES[-2:]
 before={p:digest(p) for p in generated}
 subprocess.run(['python3','python/develop_new_work_lean.py'],cwd=ROOT,check=True)
 assert before=={p:digest(p) for p in generated},'generated proofs differ from retained receipts'
 audit='\n'.join('import '+p.removesuffix('.lean').replace('/','.') for p in MODULES)+'\n'
 audit+='\n'.join('#print axioms '+n for n in names)+'\n'
 assert (ROOT/'audit/NewWorkClosure.lean').read_text()==audit,'audit entry point differs from source declarations'
 out=ROOT/'receipts/new_work_lean';out.mkdir(exist_ok=True)
 for path in MODULES:
  dest=ROOT/'.lake/build/lib/lean'/Path(path).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  run=subprocess.run(['lake','env','lean','-o',str(dest),path],cwd=ROOT,text=True,capture_output=True)
  (out/(Path(path).stem+'.log')).write_text(run.stdout+run.stderr)
  if run.returncode or run.stdout.strip() or run.stderr.strip():raise RuntimeError('compile failed or unexpected compiler output: '+path+'\n'+run.stdout+run.stderr)
 run=subprocess.run(['lake','env','lean','audit/NewWorkClosure.lean'],cwd=ROOT,text=True,capture_output=True,check=True)
 pattern=re.compile(r"'([^']+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])")
 records=list(pattern.finditer(run.stdout))
 if [m.group(1) for m in records]!=names or pattern.sub('',run.stdout).strip() or run.stderr.strip():raise RuntimeError('incomplete/unparsed axiom audit')
 allowed={'propext','Quot.sound','Classical.choice'};parsed=[]
 for m in records:
  axioms=[a.strip() for a in (m.group(2) or '').split(',') if a.strip()]
  if set(axioms)-allowed:raise RuntimeError('nonstandard axioms: '+m.group(1))
  parsed.append({'declaration':m.group(1),'axioms':axioms})
 (out/'axioms.log').write_text(run.stdout)
 receipt={'schema':'pp-new-work-lean/1','compiled':True,'lean_version':'4.20.0',
  'declarations':parsed,'declaration_count':len(parsed),'all_future_quotient_models':324,
  'source_sha256':{p:digest(p) for p in MODULES+INPUTS+['audit/NewWorkClosure.lean','scripts/check_new_work_lean.py']},
  'scope':'compiled theorem statements and retained literal instances; no whole-Python refinement; no unconditional formal elliptic rank identity'}
 (out/'verification.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'compiled':True,'declarations':len(parsed),'models':324,'standard_axioms_only':True}))
if __name__=='__main__':main()
