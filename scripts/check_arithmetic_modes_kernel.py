"""Kernel-check signed semantics, group algebra and literal multimode graphs."""
import sys,os,re,time,json,tempfile,subprocess,shutil,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'python'))
from perfectpower.arithmetic_modes import Mode,ModePopulation,signed_ballot

def main():
    binary=os.environ.get('PERFECTPOWER_LEAN') or shutil.which('lean')
    if not binary:raise RuntimeError('Lean 4.20.0 required')
    version=subprocess.check_output([binary,'--version'],text=True).strip();assert version.startswith('Lean (version 4.20.0,')
    core=ROOT/'PerfectPower/ArithmeticHeightPauli.lean';source=ROOT/'PerfectPower/ArithmeticModes.lean'
    raw=source.read_text();names=re.findall(r'^theorem (\w+)',raw,re.M)
    assert not re.search(r'\b(sorry|native_decide|axiom)\b',re.sub(r'/\-.*?\-/','',raw,flags=re.S))
    generated=['set_option maxRecDepth 8192','namespace PerfectPower.ArithmeticModes.Fixtures'];literal=[]
    for p,q in ((2,3),(2,5),(3,5),(5,7)):
        for d in range(1,7):
            name=f'signed_{p}_{q}_{d}';val=signed_ballot(p,q,d)
            generated.append(f'theorem {name} : signedBallot {p} {q} {d} {d} = ({val} : Int) := by simp only [signedBallot,sign]; decide')
            literal.append(name)
    specs=[([Mode(2,1,2,1),Mode(3,-1,2,2)],9,9,True,None),
        ([Mode(2,-1,1,1),Mode(3,-1,1,2),Mode(5,1,1,3),Mode(7,1,1,1)],6,35,True,None),
        ([Mode(2,1,1,1),Mode(3,-1,1,2),Mode(5,1,1,3)],1,5,False,None),
        ([Mode(2,1,2,1),Mode(3,-1,2,2)],9,9,True,{'initial':0,'accepting':[0,1,2],'transitions':[[1,2],[None,2],[1,None]]})]
    packets=[]
    for i,(modes,start,cap,integral,controller) in enumerate(specs):
        pop=ModePopulation(modes,start,cap,integral,controller);keys=[key for layer in pop.layers for key in layer];ids={key:j for j,key in enumerate(keys)}
        table=[[next(('some '+str(ids[c]) for a,c in pop.edges.get(key,()) if a==j),'none') for j in range(len(modes))] for key in keys]
        graph='['+','.join('['+','.join(row)+']' for row in table)+']'
        accepting=[ids[key] for key in keys if key[0]==pop.quotas and key[1] in pop.accepting]
        generated.append(f'def edges_{i} : List (List (Option Nat)) := {graph}')
        generated.append(f'def next_{i} (s a : Nat) : Option Nat := (edges_{i}.getD s []).getD a none')
        generated.append(f'def accept_{i} (s : Nat) : Bool := ({accepting} : List Nat).contains s')
        name=f'population_{i}'
        generated.append(f'theorem {name} : census {list(range(len(modes)))} next_{i} accept_{i} {pop.length} 0={pop.count} := by decide')
        literal.append(name)
        # Explicit finite adapter: complete outgoing actions plus reduced rational height.
        checks=[]
        for key in keys:
            counts,q=key;value=pop.values[key]
            for j,m in enumerate(modes):
                nn=value.numerator*(m.prime if m.direction==1 else 1);dd=value.denominator*(1 if m.direction==1 else m.prime)
                from math import gcd
                g=gcd(nn,dd);n,d=nn//g,dd//g
                t=pop.transition[q][j]
                allowed=counts[j]<m.quota and t is not None and (not integral or d==1) and max(n,d)<=cap
                child=pop.advance(key,j)
                assert (child is not None)==allowed
                a=f'decide ({counts[j]} < {m.quota}) && '+('false' if t is None else 'true')
                a+=f' && '+(f'decide ({dd} / Nat.gcd {nn} {dd} = 1)' if integral else 'true')
                a+=f' && decide (max ({nn}/Nat.gcd {nn} {dd}) ({dd}/Nat.gcd {nn} {dd}) ≤ {cap})'
                checks.append(f'({a}) = (next_{i} {ids[key]} {j}).isSome')
                checks.append(f'next_{i} {ids[key]} {j} = '+('some '+str(ids[child]) if child is not None else 'none'))
                if child is not None:
                    checks.append(f'({pop.values[child].numerator} * {dd} = {nn} * {pop.values[child].denominator})')
                    target=child[0];checks.extend(f'({target[k]} = {counts[k]} + {1 if k==j else 0})' for k in range(len(modes)))
                    checks.append(f'({child[1]} = {t})')
        name=f'complete_edges_{i}'
        statement='(['+','.join('decide ('+c+')' for c in checks)+'] : List Bool).all id=true'
        generated.append(f'set_option maxHeartbeats 4000000 in theorem {name} : '+statement+' := by decide');literal.append(name)
        packets.append({'model':i,'nodes':len(keys),'horizon':pop.length,'count':str(pop.count),'complete_action_checks':len(keys)*len(modes),'scalar_checks':len(checks)})
    generated.append('end PerfectPower.ArithmeticModes.Fixtures')
    statements='\n'.join(generated)+'\n';audit=core.read_text().replace('import Std','import Std\nset_option maxRecDepth 8192',1)+'\n'+raw.split('\n',1)[1]+'\n'+statements
    audit+=''.join(f'#print axioms PerfectPower.ArithmeticModes.{name}\n' for name in names)
    audit+=''.join(f'#print axioms PerfectPower.ArithmeticModes.Fixtures.{name}\n' for name in literal)
    t=time.perf_counter()
    with tempfile.TemporaryDirectory() as tmp:
        p=Path(tmp)/'ModesAudit.lean';p.write_text(audit)
        run=subprocess.run([binary,str(p)],cwd=ROOT,capture_output=True,text=True,timeout=240)
    log=run.stdout+run.stderr
    if run.returncode or 'warning:' in log:raise RuntimeError(log)
    axioms=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)+[(n,'') for n in re.findall(r"'([^']+)' does not depend on any axioms",log)]
    assert len(axioms)==len(names)+len(literal)
    for name,a in axioms:assert {x.strip() for x in a.split(',') if x.strip()}<={'propext','Quot.sound','Classical.choice'},(name,a)
    out=ROOT/'receipts/arithmetic_modes';out.mkdir(exist_ok=True,parents=True)
    (out/'kernel.log').write_text(log);(out/'literal_fixtures.lean').write_text('import PerfectPower.ArithmeticModes\n'+statements)
    receipt={'status':'passed','lean_version':version,'generic_theorems':len(names),'literal_theorems':len(literal),'seconds':time.perf_counter()-t,
        'models':packets,'axioms':{n:[x.strip() for x in a.split(',') if x.strip()] for n,a in axioms},
        'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (core,source,Path(__file__),ROOT/'python/perfectpower/arithmetic_modes.py')},
        'scope':'Signed weighted enumeration, general partial-state word semantics, distinct enumeration, language/weighted transport, 16-element Pauli group and Gaussian matrix representation, square-height wall theorem, 24 signed values, four literal graph counts and complete scalar edge checks.',
        'open':'Generic Python compiler refinement, infinite-dimensional operators and asymptotic laws remain outside this kernel account.'}
    (out/'kernel.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ('status','generic_theorems','literal_theorems','seconds')}))
if __name__=='__main__':main()
