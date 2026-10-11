"""Check all geometry certificates and require arithmetic mutations to fail."""
from pathlib import Path
from hashlib import sha256
import json,os,re,subprocess,tempfile

root=Path.cwd();out=root/'receipts/geometry_certificates'
lean=os.environ.get('PERFECTPOWER_LEAN','lean')
accepted={};rejected={};log=[];negative=[]
names=['SteinerFan','TJunction','Concave','RationalMesh','SquareRoute','ZeroRoute','RationalRoute','Unreachable']
with tempfile.TemporaryDirectory() as directory:
    temp=Path(directory);(temp/'PerfectPower').mkdir()
    env=dict(os.environ);env['LEAN_PATH']=str(temp)+(':'+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    def run(path,cwd=root,extra=()):
        return subprocess.run([lean,*extra,str(path)],cwd=cwd,env=env,capture_output=True,text=True)
    foundation=root/'PerfectPower/GeometryCertificates.lean'
    result=run(foundation,extra=('-o',str(temp/'PerfectPower/GeometryCertificates.olean')))
    log.append(result.stdout+result.stderr)
    if result.returncode or 'sorryAx' in log[-1]:raise RuntimeError('generic foundation rejected: '+log[-1])
    accepted['GeometryCertificates']=sha256(foundation.read_bytes()).hexdigest()
    for name in names:
        path=out/(name+'.lean');result=run(path);output=result.stdout+result.stderr;log.append(output)
        if result.returncode or 'sorryAx' in output:raise RuntimeError(name+' rejected: '+output)
        accepted[name]=sha256(path.read_bytes()).hexdigest()
    square=(out/'SquareRoute.lean').read_text();fan=(out/'SteinerFan.lean').read_text();cut=(out/'Unreachable.lean').read_text()
    bad_boundary=fan.replace('def meshEdges : List (Point × Point) := [','def meshEdges : List (Point × Point) := [(((0 : Int),(0 : Int)),((4 : Int),(0 : Int))), ',1)
    variants={
        'infeasible-potential':(square,square.replace('(0 : Int), (6 : Int)','(0 : Int), (7 : Int)',1)),
        'false-cut':(cut,cut.replace('theorem target_outside : ¬reachable 1','theorem target_outside : ¬reachable 0',1)),
        'false-total-area':(fan,re.sub(r'(theorem area_total .*?)=\(32 : Int\)',r'\1=(33 : Int)',fan,count=1)),
        'false-separation':(fan,re.sub(r'(theorem separation_0_1 .*?)\(1\) := by decide',r'\1(-1) := by decide',fan,count=1)),
        'wrong-boundary-count':(fan,bad_boundary),
    }
    for name,(original,source) in variants.items():
        if original==source:raise AssertionError('mutation did not apply: '+name)
        path=temp/'Rejected.lean';path.write_text(source)
        result=run(path,cwd=temp);output=result.stdout+result.stderr
        # A missing tool, import, or root directory failure is not a rejection.
        if result.returncode==0 or "tactic 'decide'" not in output:
            raise AssertionError(name+' did not fail by kernel-checked arithmetic: '+output)
        rejected[name]=sha256(source.encode()).hexdigest();negative.append(name+': rejected\n'+output)
(out/'kernel-tests.log').write_text('\n'.join(log))
(out/'kernel-rejections.log').write_text('\n'.join(negative))
validation={'schema':'pp-geometry-certificate-validation/1','kernel_checked':True,
            'accepted_source_sha256':accepted,'rejected_source_sha256':rejected,
            'lean_version':subprocess.check_output([lean,'--version'],text=True).strip(),
            'scope':'accepted source hashes only; topology and source geometry remain Python'}
(out/'kernel-validation.json').write_text(json.dumps(validation,sort_keys=True,indent=2)+'\n')
print('Accepted generic foundations and '+str(len(names))+' source-bound certificates; rejected '+str(len(rejected))+' arithmetic mutations.')
