"""Kernel-check geometry interpreted certificates and deliberate corruptions.

Requires pinned Mathlib on LEAN_PATH (normally run through lake env). Compilation
errors, stale hashes and missing tools cannot count as successful validation.
"""
from pathlib import Path
from hashlib import sha256
import json,os,re,subprocess,tempfile

root=Path.cwd();out=root/'receipts/geometry_admission'
lean=os.environ.get('PERFECTPOWER_LEAN','lean')
accepted={};rejected={};logs=[];negative=[]
names=['Square','Concave','Tangent','BoundaryOverlap','Rational','Zero','Disconnected','Refinement','ContactOverlap','ContactTangent','ContactDisjoint','ContactCrossing']
with tempfile.TemporaryDirectory() as directory:
    temp=Path(directory);(temp/'PerfectPower').mkdir()
    env=dict(os.environ);env['LEAN_PATH']=str(temp)+(':'+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    def run(path,extra=()):
        return subprocess.run([lean,*extra,str(path)],cwd=root,env=env,capture_output=True,text=True,timeout=900)
    for module in ('GeometryCertificates','GeometryAdmission','GeometrySourceTransport','GeometryContact'):
        path=root/'PerfectPower'/(module+'.lean')
        before=path.read_bytes()
        result=run(path,('-o',str(temp/'PerfectPower'/(module+'.olean'))))
        output=result.stdout+result.stderr;logs.append(output)
        if result.returncode or 'sorryAx' in output:raise RuntimeError(module+' rejected: '+output)
        if before!=path.read_bytes():raise AssertionError('source changed during check: '+module)
        accepted[module]=sha256(before).hexdigest();print('Accepted '+module,flush=True)
    for name in names:
        path=out/(name+'.lean');metadata=json.loads((out/(name+'.json')).read_text())
        digest=sha256(path.read_bytes()).hexdigest()
        if digest!=metadata['proof']['source_sha256']:raise AssertionError('stale source hash: '+name)
        result=run(path);output=result.stdout+result.stderr;logs.append(output)
        if result.returncode or 'sorryAx' in output:raise RuntimeError(name+' rejected: '+output)
        if digest!=sha256(path.read_bytes()).hexdigest():raise AssertionError('source changed during check: '+name)
        accepted[name]=digest;print('Accepted '+name,flush=True)
    square=(out/'Square.lean').read_text();refinement=(out/'Refinement.lean').read_text()
    # All mutations affect geometry/source reconstruction, not only potentials.
    variants={
        'dropped-valid-edge':(square,square.replace('def admitted : List (Nat × Nat) := [(0,2),','def admitted : List (Nat × Nat) := [',1)),
        'wrong-manhattan-weight':(square,square.replace('theorem source_edges : edges.Perm [(0,2,(2 : Int))','theorem source_edges : edges.Perm [(0,2,(3 : Int))',1)),
        'invented-blocked-edge':(square,square.replace('def admitted : List (Nat × Nat) := [','def admitted : List (Nat × Nat) := [(0,1),',1)),
        'changed-source-coordinate':(square,square.replace('def sourceStart : Point := ((-1 : Int),(1 : Int))','def sourceStart : Point := ((-2 : Int),(1 : Int))',1)),
        'false-blocked-parameter':(square,re.sub(r'(theorem blockage_0_1 .*?\.eval )\(\(1 : ℚ\)/\(2 : ℚ\)\)',r'\1((0 : ℚ)/(1 : ℚ))',square,count=1)),
        'partition-gap':(square,re.sub(r'(def cells_0_2 .*? := )\[.*?\]\n',r'\1[((0 : ℚ),(1/4 : ℚ)),((1/2 : ℚ),(1 : ℚ))]\n',square,count=1)),
        'false-refinement-ratio':(refinement,refinement.replace('((1 : ℚ)/(2 : ℚ)) (by norm_num)','((1 : ℚ)/(3 : ℚ)) (by norm_num)',1)),
    }
    for name,(original,source) in variants.items():
        if original==source:raise AssertionError('mutation did not apply: '+name)
        path=temp/'Rejected.lean';path.write_text(source)
        result=run(path);output=result.stdout+result.stderr
        if result.returncode==0 or 'error:' not in output or any(s in output for s in ('unknown module','unknown package','failed to locate','file not found','maximum recursion','maximum number of heartbeats')):
            raise AssertionError('not a mathematical rejection: '+name+'\n'+output)
        if name!='false-refinement-ratio' and "tactic 'decide'" not in output:
            raise AssertionError('mutation failed for another reason: '+name+'\n'+output)
        rejected[name]=sha256(source.encode()).hexdigest();negative.append(name+'\n'+output)
        print('Rejected '+name,flush=True)
(out/'kernel-tests.log').write_text('\n'.join(logs))
(out/'kernel-rejections.log').write_text('\n'.join(negative))
validation={'schema':'pp-geometric-admission-validation/1','kernel_checked':True,
    'accepted_source_sha256':accepted,'rejected_source_sha256':rejected,
    'lean_version':subprocess.check_output([lean,'--version'],text=True).strip(),
    'scope':'exact accepted hashes: universal rational winding segment avoidance, complete source-derived finite graph, graph Manhattan optimality/unreachability, pointwise triangular-source refinement coverage; general polygon topology and arbitrary mesh coverage remain open'}
(out/'kernel-validation.json').write_text(json.dumps(validation,sort_keys=True,indent=2)+'\n')
print('Accepted '+str(len(accepted))+' sources; rejected '+str(len(rejected))+' geometry mutations.')
