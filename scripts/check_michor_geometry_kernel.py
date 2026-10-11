"""Replay exact differential coefficient and continuum bridge proofs in Lean.

Use `lake env python3 scripts/check_michor_geometry_kernel.py` after lake update.
PERFECTPOWER_LEAN can select an installed Lean 4.20.0 binary.
"""
from pathlib import Path
from hashlib import sha256
import json,os,re,subprocess,tempfile
root=Path(__file__).resolve().parents[1];out=root/'receipts/michor_geometry'
lean=os.environ.get('PERFECTPOWER_LEAN','lean');accepted={};rejected={};logs=[];negatives=[]
with tempfile.TemporaryDirectory(prefix='pp-michor-kernel-') as directory:
    temp=Path(directory);(temp/'PerfectPower').mkdir()
    env=dict(os.environ);env['LEAN_PATH']=str(temp)+(':'+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    def run(path,extra=(),cwd=root):
        live=temp/'current.log'
        with live.open('w') as stream:
            try:r=subprocess.run([lean,*extra,str(path)],cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT,text=True,timeout=1800)
            except subprocess.TimeoutExpired:
                stream.flush();(out/'kernel-timeout.log').write_text(live.read_text());raise
        r.stdout=live.read_text();r.stderr='';return r
    for name in ['BernsteinBoxes','MichorGeometry']:
        print('Checking foundation '+name,flush=True)
        p=root/'PerfectPower'/(name+'.lean');r=run(p,('-o',str(temp/'PerfectPower'/(name+'.olean'))))
        output=r.stdout+r.stderr;logs.append(output)
        if r.returncode or 'sorryAx' in output:raise RuntimeError(name+': '+output)
        for group in re.findall(r'depends on axioms: \[(.*?)\]',output,re.S):
            if any(a.strip() not in {'propext','Classical.choice','Quot.sound'} for a in group.split(',') if a.strip()):raise AssertionError('unexpected foundation axiom: '+group)
        accepted[str(p.relative_to(root))]=sha256(p.read_bytes()).hexdigest()
    for p in sorted(out.glob('*.lean')):
        print('Checking generated source '+p.name,flush=True)
        source_hash=sha256(p.read_bytes()).hexdigest()
        metadata=json.loads(p.with_name(p.stem+'-proof.json').read_text())
        if sha256(p.read_bytes()).hexdigest()!=metadata['source_sha256']:
            raise AssertionError('proof packet hash mismatch: '+p.name)
        if re.search(r'\b(?:sorry|axiom|native_decide)\b',p.read_text()):
            raise AssertionError('unexpected trust escape: '+p.name)
        r=run(p);output=r.stdout+r.stderr;logs.append(output)
        if r.returncode or 'sorryAx' in output:raise RuntimeError(p.name+' exit='+str(r.returncode)+': '+output)
        for group in re.findall(r'depends on axioms: \[(.*?)\]',output,re.S):
            if any(a.strip() not in {'propext','Classical.choice','Quot.sound'} for a in group.split(',') if a.strip()):
                raise AssertionError('unexpected theorem axiom: '+group)
        if sha256(p.read_bytes()).hexdigest()!=source_hash:raise AssertionError('source changed during proof replay: '+p.name)
        accepted[str(p.relative_to(root))]=source_hash
    # These fail in arithmetic tactics, not because of an absent import.
    sphere=(out/'SphereDynamics.lean').read_text()
    gradient=sphere.replace('theorem log_gradient_0_denominator (x y : ℝ) : 2*','theorem log_gradient_0_denominator (x y : ℝ) : 3*',1)
    foundation=(root/'PerfectPower/MichorGeometry.lean').read_text()
    energy=foundation.replace('2*(u*accelX gx gy u v+v*accelY gx gy u v)','3*(u*accelX gx gy u v+v*accelY gx gy u v)',1)
    upper=foundation.replace('planeDensity x y ≤ 2 :=','planeDensity x y ≤ 1 :=',1)
    curve=(out/'FiniteBridge.lean').read_text()
    wrong_scale=curve.replace('((1 : ℝ)/4)^2 <','(1 : ℝ)^2 <',1)
    for name,original,source in [('false-curve-scale',curve,wrong_scale),('wrong-gradient-factor',sphere,gradient),('wrong-energy-factor',foundation,energy),('false-global-upper',foundation,upper)]:
        if original==source:raise AssertionError('mutation missed '+name)
        p=temp/'Rejected.lean';p.write_text(source);r=run(p,cwd=temp);output=r.stdout+r.stderr
        if not r.returncode or not any(marker in output for marker in ['unsolved goals','failed','linarith','type mismatch']):raise AssertionError(name+': '+output)
        if any(marker in output for marker in ['unknown module','object file','unknown namespace']):raise AssertionError('invalid rejection '+output)
        rejected[name]=sha256(source.encode()).hexdigest();negatives.append(name+'\n'+output)
(out/'kernel-tests.log').write_text('\n'.join(logs))
(out/'kernel-rejections.log').write_text('\n'.join(negatives))
validation={'schema':'pp-michor-kernel-validation/1','kernel_checked':True,'accepted_source_sha256':accepted,
            'rejected_source_sha256':rejected,'lean_version':subprocess.check_output([lean,'--version'],env=env,text=True).strip(),
            'scope':'hash-bound coefficient identities, generic energy/transport algebra, continuum domain inequalities, common-path infimum transfer; ODE existence and analytic derivative interpretation are not Lean formalized'}
(out/'kernel-validation.json').write_text(json.dumps(validation,sort_keys=True,indent=2)+'\n')
print(f'Accepted {len(accepted)} Lean sources; rejected {len(rejected)} arithmetic mutations.')
