"""Replay all-real geometry and analytic proofs, then reject false arithmetic claims."""
from pathlib import Path
from hashlib import sha256
from concurrent.futures import ThreadPoolExecutor
import json,os,re,subprocess,tempfile,sys,resource
soft,hard=resource.getrlimit(resource.RLIMIT_STACK)
resource.setrlimit(resource.RLIMIT_STACK,(min(268435456,hard) if hard != resource.RLIM_INFINITY else 268435456,hard))
root=Path.cwd();out=root/'receipts/planar_closure';lean=os.environ.get('PERFECTPOWER_LEAN','lean')
accepted={};rejected={};positive=[];negative=[];reused={}
previous={}
if '--extend' in sys.argv:
    previous=json.loads((out/'kernel-validation.json').read_text())['accepted_source_sha256']
    positive.append((out/'kernel-tests.log').read_text())
modules=['GeometryCertificates','GeometryAdmission','GeometrySourceTransport','RiemannianEnergy',
 'PlanarCertificates','PlanarGeometry','RealVisibility','RealContact','FlatRiemannian','MetricJetRealization','MetricJetConnection']
with tempfile.TemporaryDirectory() as directory:
    temp=Path(directory);(temp/'PerfectPower').mkdir()
    env=dict(os.environ);env['LEAN_PATH']=str(temp)+(':'+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    def run(path,extra=()):
        return subprocess.run([lean,'-s','262144',*extra,str(path)],cwd=root,env=env,capture_output=True,text=True,timeout=1800)
    def accept(path,extra=()):
        before=path.read_bytes();name=path.stem
        if path.parent==out:
            meta=json.loads(path.with_suffix('.json').read_text())
            if sha256(before).hexdigest()!=meta['proof']['source_sha256']:raise AssertionError('stale source hash: '+name)
        if path.parent==out and previous.get(name)==sha256(before).hexdigest():
            reused[name]=sha256(before).hexdigest();print('Retained exact accepted source '+name,flush=True)
            return name,sha256(before).hexdigest(),name+' retained from preceding exact-source replay'
        result=run(path,extra);log=result.stdout+result.stderr
        if result.returncode or any(bad in log for bad in ('sorryAx','ofReduceBool')):raise RuntimeError(name+' failed: '+log)
        for block in re.findall(r'depends on axioms: \[(.*?)\]',log,re.S):
            unexpected=set(x.strip() for x in block.split(',') if x.strip())-{'propext','Classical.choice','Quot.sound'}
            if unexpected:raise RuntimeError('unexpected axioms: '+str(unexpected))
        if re.search(r'(?m)^\s*(axiom\s|.*\bsorry\b|.*\bnative_decide\b)',before.decode()):raise RuntimeError('untrusted source proof: '+name)
        if before!=path.read_bytes():raise AssertionError('source changed during validation')
        print('Accepted '+name,flush=True)
        return name,sha256(before).hexdigest(),name+'\n'+log
    for module in modules:
        name,digest,log=accept(root/'PerfectPower'/(module+'.lean'),('-o',str(temp/'PerfectPower'/(module+'.olean'))))
        accepted[name]=digest;positive.append(log)
    with ThreadPoolExecutor(max_workers=2) as pool:
        for name,digest,log in pool.map(accept,sorted(out.glob('*.lean'))):
            accepted[name]=digest;positive.append(log)
    header='import PerfectPower.PlanarCertificates\nopen PerfectPower.PlanarCertificates\n'
    # Each expected rejection is a false closed arithmetic proposition, not a syntax or resource failure.
    variants={
      'empty-farkas-witness':header+'example : contradiction [((0,0,-1),false)] [] := by decide +kernel\n',
      'negative-weight':header+'example : contradiction [((0,0,1),false)] [(((0,0,1),false),-1)] := by decide +kernel\n',
      'foreign-constraint':header+'example : contradiction [] [(((0,0,-1),false),1)] := by decide +kernel\n',
      'nonzero-slope':header+'example : contradiction [((1,0,-1),false)] [(((1,0,-1),false),1)] := by decide +kernel\n',
      'nonstrict-zero':header+'example : contradiction [((0,0,0),false)] [(((0,0,0),false),1)] := by decide +kernel\n',
      'zero-weight-strict':header+'example : contradiction [((0,0,0),true)] [(((0,0,0),true),0)] := by decide +kernel\n',
      'unbound-leaf':header+'example : checked (.eq (1,0,0)) [] .leaf := by decide +kernel\n',
      'false-boundary-sign':header+'example : checked (.eq (1,0,0)) [((1,0,0),1)] .leaf := by decide +kernel\n',
    }
    crossing=(out/'Crossing.lean').read_text()
    variants['false-real-blocked-parameter']=re.sub(r'blockedFormula polygons start finish \(\([^\n]+? = true',
        'blockedFormula polygons start finish ((0 : ℚ)/(1 : ℚ)) = true',crossing,count=1)
    if variants['false-real-blocked-parameter']==crossing:raise AssertionError('blocked mutation did not apply')
    for name,source in variants.items():
        path=temp/'Rejected.lean';path.write_text(source);result=run(path);log=result.stdout+result.stderr
        if result.returncode==0 or "tactic 'decide'" not in log or any(s in log for s in ('unknown module','failed to locate','maximum recursion','maximum number of heartbeats')):
            raise AssertionError('not a mathematical rejection: '+name+'\n'+log)
        rejected[name]=sha256(source.encode()).hexdigest();negative.append(name+'\n'+log)
        print('Rejected '+name,flush=True)
(out/'kernel-tests.log').write_text('\n'.join(positive))
(out/'kernel-rejections.log').write_text('\n'.join(negative))
receipt={'schema':'pp-planar-closure-kernel-validation/1','kernel_checked':True,
 'accepted_source_sha256':accepted,'rejected_source_sha256':rejected,'reused_source_sha256':reused,
 'lean_version':subprocess.check_output([lean,'--version'],text=True).strip(),
 'scope':'all-real source winding visibility and mesh coverage, source graph completeness, all-finite-source-walk Manhattan bounds, flat analytic geodesics and segment integral energy, smooth local metric-jet realization and connection; no Jordan or arbitrary continuous path completeness claim'}
(out/'kernel-validation.json').write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
print('Accepted',len(accepted),'sources; rejected',len(rejected),'mathematical corruptions.')
