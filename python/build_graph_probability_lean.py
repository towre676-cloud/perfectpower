"""Replay rational graph laws, including models with nonrational unnormalized weights."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib,json
from perfectpower.connection_polytope import ConnectionGraph
ROOT=Path(__file__).resolve().parents[1]
def rat(x):
 q=Q(x);return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
def vec(x):return '!['+','.join(x)+']'
def mat(x):return '!!['+';'.join(','.join(rat(v) for v in row) for row in x)+']'
def elimination(matrix):
 n=len(matrix);u=[list(map(Q,row)) for row in matrix];e=[[Q(int(i==j)) for j in range(n)] for i in range(n)]
 for j in range(n):
  if not u[j][j]:
   assert all(not u[i][j] for i in range(j+1,n)), 'pivot exchange requires an additional witness'
   continue
  for i in range(j+1,n):
   c=u[i][j]/u[j][j]
   u[i]=[x-c*y for x,y in zip(u[i],u[j])]
   e[i]=[x-c*y for x,y in zip(e[i],e[j])]
 value=Q(1)
 for j in range(n):value*=u[j][j]
 return e,u,value

def build():
 src=ROOT/'receipts/monograph_development/connection_corpus.json';old=ROOT/'receipts/positive_geometry/connection_polytopes.json'
 rows=json.loads(src.read_text())['rows'];polys=json.loads(old.read_text());models={};mapping=[]
 for row in rows:
  m=row['measure']
  if m['status']!='EXACT_BASIS_MEASURE' or any(len(v)!=1 for line in m['transfer_kernel'] for v in line):continue
  p=polys[row['source_row']]['polytope'];g=ConnectionGraph(p['vertices'],tuple(p['edges']),p['power']);field=g.field
  decode=lambda v:field.element([Q(x) for x in v])
  z=decode(p['determinant']);weights=[Q(x) for x in p['weights']];outcomes=[];prob=[]
  for term in p['terms']:
   v=decode(term['coefficient'])
   for i in term['edges']:v=v*weights[i]
   v=v*z.inverse()
   assert len(v.coefficients)==1,(row['source_row'],v)
   outcomes.append(term['edges']);prob.append(str(v.coefficients[0]))
  model={'kernel':[[v[0] for v in line] for line in m['transfer_kernel']],'outcomes':outcomes,'weights':prob}
  key=json.dumps(model,sort_keys=True)
  if key not in models:models[key]=model
  mapping.append({'source_row':row['source_row'],'model':list(models).index(key),'power':m['power']})
 modules=[]
 for idx,model in enumerate(models.values()):
  m=len(model['kernel']);r=len(model['weights']);name=f'GraphProbability{idx:02d}'
  header=f'namespace PerfectPower.{name}\nopen Matrix\nopen scoped BigOperators\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
  end=f'end PerfectPower.{name}\n'
  data=f'''import PerfectPower.FiniteGraphProbability
{header}def K : Matrix (Fin {m}) (Fin {m}) ℚ := {mat(model['kernel'])}
def O : Fin {r} → Finset (Fin {m}) := {vec(['{'+','.join(map(str,s))+'}' for s in model['outcomes']])}
def w : Fin {r} → ℚ := {vec([rat(x) for x in model['weights']])}
theorem nonnegative : ∀ o, 0 ≤ w o := by decide +kernel
theorem normalized : ∑ o,w o=1 := by decide +kernel
{end}'''
  dataname=name+'Data';modules.append('Generated/'+dataname)
  (ROOT/'PerfectPower/Generated'/(dataname+'.lean')).write_text(data)
  sets=['{'+','.join(str(i) for i in range(m) if mask>>i&1)+'}' if mask else '∅' for mask in range(1<<m)]
  checks=[]
  for j,S in enumerate(sets):
   a=[[Q(model['kernel'][i][k]) if j>>i&1 else Q(int(i==k)) for k in range(m)] for i in range(m)]
   e,u,value=elimination(a)
   text=f'theorem inclusion_{j:03d} : det (DeterminantalEvents.padded K ({S} : Finset (Fin {m})))=FiniteGraphProbability.inclusion w O ({S} : Finset (Fin {m})) := by\n'
   text+=f'  have hd : det (DeterminantalEvents.padded K ({S} : Finset (Fin {m})))=({rat(value)} : ℚ) :=\n'
   text+=f'    TriangularDeterminant.checked _ ({mat(e)}) ({mat(u)}) (by unfold Matrix.BlockTriangular; decide +kernel) (by decide +kernel) (by decide +kernel) (by unfold Matrix.BlockTriangular; decide +kernel) _ (by decide +kernel)\n'
   text+=f'  have hm : FiniteGraphProbability.inclusion w O ({S} : Finset (Fin {m}))=({rat(value)} : ℚ) := by decide +kernel\n  exact hd.trans hm.symm\n'
   checks.append(text)
  chunks=[]
  for start in range(0,len(checks),8):
   chunk=name+f'Moments{start//8:02d}';chunks.append(chunk);modules.append('Generated/'+chunk)
   text=f'import PerfectPower.Generated.{dataname}\nimport PerfectPower.TriangularDeterminant\n'+header+''.join(checks[start:start+8])+end
   (ROOT/'PerfectPower/Generated'/(chunk+'.lean')).write_text(text)
  def cases(i,mask,indent):
   if i==m:
    return indent+f'have hs : S=({sets[mask]} : Finset (Fin {m})) := by\n'+indent+'  ext i; fin_cases i <;> simp_all\n'+indent+f'rw [hs]\n'+indent+f'exact inclusion_{mask:03d}\n'
   return indent+f'by_cases h{i} : ({i} : Fin {m}) ∈ S\n'+indent+'· '+cases(i+1,mask|(1<<i),indent+'  ').lstrip()+indent+'· '+cases(i+1,mask,indent+'  ').lstrip()
  aggregate=''.join(f'import PerfectPower.Generated.{chunk}\n' for chunk in chunks)+header
  aggregate+='theorem inclusion_checked : ∀ S, det (DeterminantalEvents.padded K S)=FiniteGraphProbability.inclusion w O S := by\n  intro S\n'+cases(0,0,'  ')
  aggregate+=f'''theorem all_events (I J : Finset (Fin {m})) (h : Disjoint I J) :
    DeterminantalEvents.mixed K I J=FiniteGraphProbability.eventMass w O I J :=
  FiniteGraphProbability.mixed_probability w O K inclusion_checked I J h
theorem probability_bounds (I J : Finset (Fin {m})) (h : Disjoint I J) :
    0 ≤ DeterminantalEvents.mixed K I J ∧ DeterminantalEvents.mixed K I J ≤ 1 := by
  rw [all_events I J h]
  exact FiniteGraphProbability.rational_event_bounds w O nonnegative normalized I J
{end}'''
  modules.append('Generated/'+name)
  (ROOT/'PerfectPower/Generated'/(name+'.lean')).write_text(aggregate)
 out=ROOT/'receipts/root_events_lean';out.mkdir(exist_ok=True)
 (out/'graph_inputs.json').write_text(json.dumps({'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'basis_source_sha256':hashlib.sha256(old.read_bytes()).hexdigest(),'source_models':len(mapping),'distinct_models':len(models),'mapping':mapping,'modules':modules},indent=2)+'\n')
 print(len(mapping),len(models))
if __name__=='__main__':build()
