"""Compile exact metric proofs and reject mathematical source corruptions."""
from pathlib import Path
from hashlib import sha256
import json,os,re,subprocess,tempfile
root=Path.cwd();out=root/'receipts/riemannian_energy';lean=os.environ.get('PERFECTPOWER_LEAN','lean')
accepted={};rejected={};positive=[];negative=[]
with tempfile.TemporaryDirectory() as directory:
    temp=Path(directory);(temp/'PerfectPower').mkdir()
    env=dict(os.environ);env['LEAN_PATH']=str(temp)+(':'+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    def run(path,extra=()):
        return subprocess.run([lean,*extra,str(path)],cwd=root,env=env,capture_output=True,text=True,timeout=900)
    sources=[root/'PerfectPower/RiemannianEnergy.lean',*sorted(out.glob('*.lean'))]
    for path in sources:
        before=path.read_bytes();name=path.stem
        if name!='RiemannianEnergy':
            meta=json.loads(path.with_suffix('.json').read_text())
            if sha256(before).hexdigest()!=meta['proof']['source_sha256']:raise AssertionError('stale source hash: '+name)
        extra=('-o',str(temp/'PerfectPower/RiemannianEnergy.olean')) if name=='RiemannianEnergy' else ()
        result=run(path,extra);log=result.stdout+result.stderr
        if result.returncode or any(bad in log for bad in ('sorryAx','ofReduceBool')):raise RuntimeError(name+' failed: '+log)
        for block in re.findall(r'depends on axioms: \[(.*?)\]',log):
            unexpected=set(x.strip() for x in block.split(',') if x.strip())-{'propext','Classical.choice','Quot.sound'}
            if unexpected:raise RuntimeError('unexpected axioms: '+str(unexpected))
        if re.search(r'(?m)^\s*(axiom\s|.*\bsorry\b|.*\bnative_decide\b)',before.decode()):raise RuntimeError('untrusted source proof: '+name)
        if before!=path.read_bytes():raise AssertionError('source changed during validation')
        accepted[name]=sha256(before).hexdigest();positive.append(name+'\n'+log)
        print('Accepted '+name,flush=True)
    detour=(out/'Detour.lean').read_text();shear=(out/'Shear.lean').read_text();jet=(out/'FirstJet.lean').read_text();straight=(out/'Straight.lean').read_text()
    variants={
      'singular-metric':detour.replace('def g : Metric ℚ := ⟨((2 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ)),((3 : ℚ)/(1 : ℚ))⟩','def g : Metric ℚ := ⟨1,1,1⟩'),
      'negative-duration':detour.replace('def durations : List ℚ := [((1 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))]','def durations : List ℚ := [-1,2]'),
      'zero-duration':detour.replace('def durations : List ℚ := [((1 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))]','def durations : List ℚ := [0,2]'),
      'changed-source':detour.replace('((1 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))','((2 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))',1),
      'dropped-duration':detour.replace('def durations : List ℚ := [((1 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ))]','def durations : List ℚ := [1]'),
      'false-affine-pullback':shear.replace('def linear : LinearMap2 ℚ := ⟨((1 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ)),((0 : ℚ)/(1 : ℚ)),((1 : ℚ)/(1 : ℚ))⟩','def linear : LinearMap2 ℚ := ⟨1,3,0,1⟩'),
      'false-connection':jet.replace('def gamma : Fin 2 → Fin 2 → Fin 2 → ℚ :=','def gamma : Fin 2 → Fin 2 → Fin 2 → ℚ := fun _ _ _ => 0\ndef discarded : Fin 2 → Fin 2 → Fin 2 → ℚ :='),
      'false-derivative':jet.replace('def D : Fin 2 → Fin 2 → Fin 2 → ℚ :=','def D : Fin 2 → Fin 2 → Fin 2 → ℚ := fun _ _ _ => 0\ndef discarded : Fin 2 → Fin 2 → Fin 2 → ℚ :='),
      'false-straight-velocity':straight.replace('def velocity : ℚ × ℚ := (((1 : ℚ)/(1 : ℚ)),((2 : ℚ)/(1 : ℚ)))','def velocity : ℚ × ℚ := (1,3)'),
    }
    for name,source in variants.items():
        original=jet if 'connection' in name or 'derivative' in name else shear if 'affine' in name else straight if 'straight' in name else detour
        if source==original:raise AssertionError('mutation did not apply: '+name)
        path=temp/'Rejected.lean';path.write_text(source)
        result=run(path);log=result.stdout+result.stderr
        if result.returncode==0 or "tactic 'decide'" not in log or any(s in log for s in ('unknown module','failed to locate','maximum recursion','maximum number of heartbeats')):
            raise AssertionError('not a mathematical rejection: '+name+'\n'+log)
        rejected[name]=sha256(source.encode()).hexdigest();negative.append(name+'\n'+log)
        print('Rejected '+name,flush=True)
(out/'kernel-tests.log').write_text('\n'.join(positive))
(out/'kernel-rejections.log').write_text('\n'.join(negative))
receipt={'schema':'pp-riemannian-kernel-validation/1','kernel_checked':True,
         'accepted_source_sha256':accepted,'rejected_source_sha256':rejected,
         'lean_version':subprocess.check_output([lean,'--version'],text=True).strip(),
         'scope':'ordered-field metric positivity, affine pullback, finite timed energy bound and rigidity, coordinate first-jet Koszul uniqueness; rational source instances; no smooth geometry, integral or obstacle geodesic completeness claim'}
(out/'kernel-validation.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
print('Accepted',len(accepted),'sources; rejected',len(rejected),'mathematical corruptions.')
