"""Untrusted discovery of Bernstein tree witnesses; Lean checks identities and coverage."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb
import hashlib,json
from perfectpower import polyalg as P
from perfectpower.sturm_fibres import root_certificate
ROOT=Path(__file__).resolve().parents[1]

def rat(x):
 q=Q(x)
 return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
def bernstein(f,a,b):
 n=len(f)-1;h=b-a
 shifted=[sum((Q(f[j])*comb(j,k)*a**(j-k)*h**k for j in range(k,n+1)),Q(0)) for k in range(n+1)]
 cs=[sum((shifted[k]*Q(comb(i,k),comb(n,k)) for k in range(i+1)),Q(0))*comb(n,i)/h**n for i in range(n+1)]
 for s in (1,-1):
  c=[s*x for x in cs]
  if all(x>=0 for x in c) and c[-1]>0:return s,c
 return None

def build():
 source=ROOT/'receipts/monograph_development/root_and_gap_examples.json';data=json.loads(source.read_text())
 certs=[('giant',data['giant_square_fibres']['fibres'][0]['certificate']),('repeated',data['repeated_and_noninteger_roots'])]
 examples=[('no_real',[1,0,1]),('fractional',[-1,2]),('negative',[-6,-1,1]),('repeated_small',[0,0,-1,0,1]),('sparse',[24,-50,35,-10,1])]
 certs += [(label,root_certificate(f)) for label,f in examples]
 out=['import PerfectPower.BernsteinRootTree','namespace PerfectPower.RootEventFixtures','open BernsteinRootTree','open scoped BigOperators','set_option maxHeartbeats 0','set_option maxRecDepth 100000']
 rows=[]
 for label,cert in certs:
  f=cert['coefficients'];B=sum(abs(x) for x in f)+1;n=len(f)-1
  anchors=sorted({node[1] for node in cert['nodes'] if node[1]-node[0]==1 and node[2]>node[3]})
  out += [f'def {label}_coefficients : List ℤ := [{",".join(map(str,f))}]',f'def {label}_F (x : ℤ) : ℚ := NativePolynomialSquare.eval {label}_coefficients x']
  nodes=[]
  def cover(a,b):
   idx=len(nodes);nodes.append(None);name=f'{label}_node{idx}'
   if b<=a:body=f'Tree.empty ({a}) ({b}) (by omega)';kind='empty'
   elif b-a==1:body=f'Tree.unit ({a})';kind='unit'
   else:
    witness=bernstein(f,a,b)
    if witness:
     s,c=witness;cname=name+'_c'
     out.append(f'def {cname} : Fin {n+1} → ℚ := ![{",".join(rat(x) for x in c)}]')
     body=f'Tree.skip ({a}) ({b}) (excludes {label}_F ({a}) ({b}) {n} {cname} ({s}) (by norm_num) (by decide +kernel) (by decide +kernel) (by intro x; simp [{label}_F,{label}_coefficients,NativePolynomialSquare.eval,form,{cname},Fin.sum_univ_succ]; ring))';kind='skip'
    else:
     options=[u for r in anchors for u in (r-1,r) if a<u<b]
     m=options[0] if options else (a+b)//2
     left=cover(a,m);right=cover(m,b)
     body=f'Tree.split ({a}) ({m}) ({b}) (by omega) (by omega) {left} {right}';kind='split'
   nodes[idx]={'a':a,'b':b,'kind':kind};out.append(f'def {name} : Tree {label}_F ({a}) ({b}) := {body}')
   return name
  tree=cover(-B-1,B);roots=cert['roots'];nameset='{' + ','.join(map(str,roots)) + '}' if roots else '∅'
  out += [f'theorem {label}_roots_checked : {tree}.roots = ({nameset} : Finset ℤ) := by decide +kernel',f'theorem {label}_complete (x : ℤ) : NativePolynomialSquare.eval {label}_coefficients x=0 ↔ x ∈ ({nameset} : Finset ℤ) := by',f'  have h := integer_complete {label}_coefficients (by decide +kernel) (by decide +kernel) {tree} x',f'  rw [{label}_roots_checked] at h', '  exact h']
  rows.append({'label':label,'degree':n,'nodes':len(nodes),'skipped':sum(x['kind']=='skip' for x in nodes),'unit':sum(x['kind']=='unit' for x in nodes),'roots':roots,'sturm_input_nodes':len(cert['nodes'])})
 out.append('end PerfectPower.RootEventFixtures')
 dest=ROOT/'PerfectPower/Generated/RootEventFixtures.lean';dest.write_text('\n'.join(out)+'\n')
 receipt=ROOT/'receipts/root_events_lean';receipt.mkdir(exist_ok=True)
 (receipt/'root_inputs.json').write_text(json.dumps({'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'module_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'rows':rows},indent=2)+'\n')
 print(rows)
if __name__=='__main__':build()
