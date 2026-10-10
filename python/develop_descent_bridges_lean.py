"""Emit kernel-checked exclusions from the retained rational two-torsion corpus."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'PerfectPower/Generated'

def z(n): return f'({n})'
def main():
 rows=json.loads((ROOT/'receipts/structural_math/two_isogeny_corpus.json').read_text())
 covers={}
 for row in rows:
  for side in ('left','right'):
   for c in row[side]['classes']:
    if c['status']=='excluded':
     key=tuple(c['cover'])
     if c['real_obstructed']:covers[key]=('real',None)
     elif key not in covers:
      t=next(t for t in c['local'] if t['obstructed'])
      covers[key]=('local',(t['prime'],t['depth']))
 files=[]
 for shard,start in enumerate(range(0,len(covers),100)):
  ns=f'PerfectPower.Generated.DescentExclusions{shard:02d}'
  lines=['import PerfectPower.LocalQuarticBridges','',f'namespace {ns}',
    'set_option maxRecDepth 100000','set_option maxHeartbeats 8000000','']
  for i,(cover,(kind,place)) in enumerate(sorted(covers.items())[start:start+100],start):
   d,a,c=map(z,cover)
   lines += [f'theorem cover_{i:04d} (u v w : ℤ) (hu : u ≠ 0) (hcop : IsRelPrime u v) :',
    f'    w^2 ≠ {d}*u^4+{a}*u^2*v^2+{c}*v^4 := by']
   if kind=='real':
    lines += [f'  exact PerfectPower.LocalQuarticBridges.primitive_real_exclusion {d} {a} {c}',
     '    u v w (by decide) (by decide) (by decide) hu']
   else:
    p,k=place;m=p**k
    lines += [f'  apply PerfectPower.LocalQuarticBridges.primitive_local_exclusion_table {d} {a} {c}',
     f'    {p} {k} (by decide) (by decide) (by decide) u v w hcop']
   # Both formal statement branches keep the same primitive-chart interface.
   lines += ['']
  lines+= [f'end {ns}','']
  path=f'PerfectPower/Generated/DescentExclusions{shard:02d}.lean'
  (ROOT/path).write_text('\n'.join(lines).replace('set_option maxHeartbeats 8000000','set_option maxHeartbeats 8000000\nset_option linter.unusedVariables false'))
  files.append(path)
 curve_packets={tuple(row[side]['curve']):row[side] for row in rows for side in ('left','right')}
 index={key:i for i,key in enumerate(sorted(covers))}
 model_files=[];models=[]
 for shard,start in enumerate(range(0,len(curve_packets),25)):
  ns=f'PerfectPower.Generated.DescentModels{shard:02d}'
  needed=sorted({index[tuple(c['cover'])]//100
   for _,packet in sorted(curve_packets.items())[start:start+25]
   for c in packet['classes'] if c['status']=='excluded'})
  lines=[f'import PerfectPower.Generated.DescentExclusions{j:02d}' for j in needed]
  lines+=['',f'namespace {ns}','set_option maxRecDepth 100000',
    'set_option maxHeartbeats 8000000','set_option linter.unusedVariables false','']
  for i,((a,b),packet) in enumerate(sorted(curve_packets.items())[start:start+25],start):
   candidates=[c['d'] for c in packet['classes']]
   survivors=packet['survivors']
   def lit(xs):return '['+','.join(map(str,xs))+']'
   tests=[];n=abs(b);p=2
   while p*p<=n:
    if n%p==0:
     tests.append(p)
     while n%p==0:n//=p
    p+=1
   if n>1:tests.append(n)
   aa,bb=z(a),z(b)
   lines += [f'theorem model_{i:04d}_support (d u v w : ℤ) (hd : Squarefree d)',
    f'    (hdb : d ∣ {bb}) (hu : u ≠ 0) (hcop : IsRelPrime u v)',
    f'    (hw : w^2=d*u^4+{aa}*u^2*v^2+({bb}/d)*v^4) :',
    f'    d ∈ ({lit(survivors)}:List ℤ) := by',
    '  have hc := PerfectPower.TwoDescentBridges.squarefree_divisor_table',
    f'    {bb} (by decide) ({lit(candidates)}:List ℤ) ({lit(tests)}:List ℤ)',
    '    (by decide) (by decide) d hd hdb',
    '  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hc',
    '  rcases hc with '+' | '.join('rfl' for _ in candidates)]
   for c in packet['classes']:
    if c['status']=='excluded':
     j=index[tuple(c['cover'])]
     lines += [f'  · exact False.elim (PerfectPower.Generated.DescentExclusions{j//100:02d}.cover_{j:04d}',
       '      u v w hu hcop hw)']
    else:lines+=['  · simp']
   lines += ['',f'theorem model_{i:04d}_rational_cover (x y : ℚ) (hx : x ≠ 0)',
    f'    (hp : y^2=x*(x^2+{aa}*x+{bb})) :',
    f'    ∃ d u v w : ℤ, d ∈ ({lit(survivors)}:List ℤ) ∧ Squarefree d ∧ d ∣ {bb} ∧',
    '      u ≠ 0 ∧ 0 < v ∧ IsRelPrime u v ∧ x=(d:ℚ)*(u:ℚ)^2/(v:ℚ)^2 ∧',
    f'      w^2=d*u^4+{aa}*u^2*v^2+({bb}/d)*v^4 ∧ y=(d:ℚ)*u*w/(v:ℚ)^3 := by',
    '  obtain ⟨d,u,v,w,hd,hdb,hu,hv,hcop,hrep,hw,hy⟩ :=',
    f'    PerfectPower.TwoDescentBridges.rational_point_cover_complete {aa} {bb} x y hx hp',
    f'  exact ⟨d,u,v,w,model_{i:04d}_support d u v w hd hdb hu hcop hw,',
    '    hd,hdb,hu,hv,hcop,hrep,hw,hy⟩','']
   models.append(dict(index=i,curve=[a,b],survivors=survivors,module=f'PerfectPower/Generated/DescentModels{shard:02d}.lean'))
  lines += [f'end {ns}','']
  path=f'PerfectPower/Generated/DescentModels{shard:02d}.lean'
  (ROOT/path).write_text('\n'.join(lines));model_files.append(path)
 manifest={'schema':'pp-descent-exclusions-lean/1','covers':[
  dict(index=i,cover=list(key),kind=value[0],place=value[1],module=files[i//100])
  for i,(key,value) in enumerate(sorted(covers.items()))], 'modules':files+model_files,'models':models,
  'scope':'primitive integral cover exclusions; no elliptic rank theorem'}
 out=ROOT/'receipts/descent_bridges';out.mkdir(exist_ok=True)
 (out/'instances.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'covers':len(covers),'modules':len(files+model_files),'models':len(models)}))
if __name__=='__main__':main()
