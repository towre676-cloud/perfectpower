"""Build kernel fixtures for rational operator word/closure certificates."""
import json,pathlib,hashlib,re
from fractions import Fraction as Q
from perfectpower import exact_linear as E
ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=ROOT/'PerfectPower/Generated';DEST=ROOT/'receipts/monograph_lean';DEST.mkdir(exist_ok=True)
def scalar(x):
 q=Q(x);return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
def matrix(rows):return '!!['+';'.join(','.join(scalar(x) for x in row) for row in rows)+']'
def vector(values):return '!['+','.join(values)+']'
def build():
 path=ROOT/'receipts/monograph_development/operator_algebras.json';raw=path.read_bytes();data=json.loads(raw)
 models=[('recurrence_'+str(i),r['profile']['algebra']) for i,r in enumerate(data['rows'])]
 models += [('example_'+str(i),r['profile']['algebra']) for i,r in enumerate(data['examples'])]
 models += [('field756',data['field756_unit_profile']['algebra'])]
 modules=[]
 for start in range(0,len(models),10):
  name=f'MonographOperators{start//10:02d}';modules.append('Generated/'+name)
  text='import PerfectPower.GeneratedOperatorAlgebra\nnamespace PerfectPower.MonographOperators\nopen Matrix\nopen scoped BigOperators\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
  for label,model in models[start:start+10]:
   B=model['basis'];G=model['operators'];n=len(B[0]);r=len(B);k=len(G)
   columns=[[Q(B[j][i//n][i%n]) for j in range(r)] for i in range(n*n)]
   decoder=[E.solve(E.transpose(columns),[int(i==j) for j in range(r)]) for i in range(r)]
   assert all(row is not None for row in decoder)
   text+=f'def {label}_B : Fin {r} → Matrix (Fin {n}) (Fin {n}) ℚ := '+vector([matrix(b) for b in B])+'\n'
   text+=f'def {label}_G : Fin {k} → Matrix (Fin {n}) (Fin {n}) ℚ := '+vector([matrix(g) for g in G])+'\n'
   text+=f'def {label}_words : Fin {r} → List (Fin {k}) := '+vector(['['+','.join(map(str,w))+']' for w in model['basis_words']])+'\n'
   coeff=model['left_generator_products']
   text+=f'def {label}_C : Fin {r} → Fin {k} → Fin {r} → ℚ := '+vector([vector([vector([scalar(x) for x in row]) for row in rows]) for rows in coeff])+'\n'
   text+=f'def {label}_X : Matrix (Fin {n*n}) (Fin {r}) ℚ := '+matrix(columns)+'\n'
   text+=f'def {label}_D : Matrix (Fin {r}) (Fin {n*n}) ℚ := '+matrix(decoder)+'\n'
   text+=f'theorem {label}_words_checked : ∀ j, GeneratedOperatorAlgebra.word {label}_G ({label}_words j)={label}_B j := by decide +kernel\n'
   text+=f'theorem {label}_products_checked : ∀ j i, {label}_G i*{label}_B j=∑ t,({label}_C j i t) • {label}_B t := by decide +kernel\n'
   text+=f'theorem {label}_decoder_checked : {label}_D*{label}_X=1 := by decide +kernel\n'
   text+=f'theorem {label}_complete : Submodule.span ℚ (Set.range {label}_B)=GeneratedOperatorAlgebra.wordSpan {label}_G := by\n'
   text+=f'  apply GeneratedOperatorAlgebra.finite_complete\n  · exact ⟨0,by decide +kernel⟩\n  · intro j;exact ⟨{label}_words j,{label}_words_checked j⟩\n  · intro i j\n    rw [{label}_products_checked j i]\n    apply Submodule.sum_mem\n    intro t ht\n    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t,rfl⟩)\n'
  text+='end PerfectPower.MonographOperators\n';(OUT/(name+'.lean')).write_text(text)
 core=['ExceptionalPowerSearch','SharpPowerGap','IntegerRootFibres','GeneratedOperatorAlgebra','ConnectionProjection','ExceptionalQuartic']
 allmodules=core+modules;audit=''.join('import PerfectPower.'+m.replace('/','.')+'\n' for m in allmodules);decls=[]
 for m in allmodules:
  src=(ROOT/'PerfectPower'/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',src,re.M).group(1)
  for t in re.findall(r'^theorem (\w+)',src,re.M):decls.append(ns+'.'+t)
 audit+=''.join('#print axioms '+n+'\n' for n in decls);(ROOT/'audit/MonographPush.lean').write_text(audit)
 receipt={'schema':'monograph-lean/1','source_sha256':hashlib.sha256(raw).hexdigest(),'operator_models':len(models),'modules':allmodules,'audited_declarations':len(decls),'module_sha256':{m:hashlib.sha256((ROOT/'PerfectPower'/(m+'.lean')).read_bytes()).hexdigest() for m in allmodules}}
 (DEST/'inputs.json').write_text(json.dumps(receipt,indent=2)+'\n')
if __name__=='__main__':build()
