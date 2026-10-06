"""Complete renormalizable holomorphic audit of a sextic-link messenger chain.
All family contractions are counted exactly; no selected CKM target is used.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations_with_replacement
from pathlib import Path
import json
import sympy as s
from math import factorial
from develop_valentiner_frames import generators,group_closure,mul,IDENTITY,product,conjugate
from develop_valentiner_invariants import Z,O,add,scale,exact_integer,symchars
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'

def census():
 elements,_,_=group_closure(generators());signatures=Counter()
 for g in elements:
  power=IDENTITY;chars=[]
  for k in range(3):
   power=mul(power,g);t=tuple(sum(F(power[1][3*i+i][j],power[0]) for i in range(3)) for j in range(4))
   h=symchars(t,3);chars.append((h[1],h[2],h[3]))
  signatures[tuple(chars)]+=1
 labels=['Lambda','A','A_tilde','B'];dimension={'Lambda':9,'A':36,'A_tilde':36,'B':100}
 rows=[]
 pairs=[]
 for a,na in signatures.items():
  for b,nb in signatures.items():
   chars=[]
   for k in range(3):
    x,y=a[k],b[k]
    chars.append([product(x[0],conjugate(y[0])),product(conjugate(x[1]),y[1]),product(x[1],conjugate(y[1])),product(x[2],y[2])])
   sym=[]
   for i in range(4):
    c=[chars[k][i] for k in range(3)]
    h=[O,c[0]]
    h.append(scale(add(product(c[0],c[0]),c[1]),F(1,2)))
    h.append(scale(add(add(product(product(c[0],c[0]),c[0]),scale(product(c[0],c[1]),3)),scale(c[2],2)),F(1,6)))
    sym.append(h)
   pairs.append((na*nb,sym))
 for degree in (1,2,3):
  for fields in combinations_with_replacement(range(4),degree):
   counts=Counter(fields);total=Z
   for n,sym in pairs:
    value=O
    for i,m in counts.items():value=product(value,sym[i][m])
    total=add(total,scale(value,F(n,1080**2)))
   d=exact_integer(total)
   rows.append({'degree':degree,'fields':[labels[i] for i in fields],'contractions':d})
 nonzero=[r for r in rows if r['contractions']]
 assert next(r['contractions'] for r in rows if r['fields']==['Lambda','Lambda','A'])==1
 assert next(r['contractions'] for r in rows if r['fields']==['Lambda','A_tilde','B'])==1
 assert next(r['contractions'] for r in rows if r['fields']==['B','B'])==1
 # The real ten-dimensional bilinear behind the sextic, independently
 # certified in the triplet coefficient field without numerical eigenvectors.
 field=s.QQ.algebraic_field(s.sqrt(5),s.sqrt(3)*s.I)
 coefficients={tuple(x['powers']):field.from_sympy(s.sympify(x['coefficient'])) for x in json.loads((OUT/'valentiner_invariants.json').read_text())['sextic']['terms']}
 monomials=[(a,b,3-a-b) for a in range(4) for b in range(4-a)]
 multiplicities=[factorial(3)//(factorial(a)*factorial(b)*factorial(c)) for a,b,c in monomials]
 tensor=[]
 for alpha in monomials:
  row=[]
  for beta in monomials:
   powers=tuple(a+b for a,b in zip(alpha,beta));mult=factorial(6)//int(__import__('math').prod(factorial(k) for k in powers))
   row.append(coefficients.get(powers,field.zero)/field.convert(mult))
  tensor.append(row)
 for i in range(10):
  for j in range(10):
   value=field.zero
   for k in range(10):value+=field.from_sympy(s.conjugate(field.to_sympy(tensor[k][i])))*multiplicities[k]*tensor[k][j]
   expected=field.from_sympy(s.Rational(8,5*multiplicities[i])) if i==j else field.zero
   assert value==expected
 result={'real_ten_bilinear_certificate':{'dimension':10,'exact_matrix_identities':100,'orthonormal_bilinear':'Q10 dagger Q10=(8/5)I','sextic':'F6(phi)=Sym3(phi)^T Q10 Sym3(phi)','nondegenerate':True},'field_dimensions':dimension,'all_degree_one_to_three_monomials':rows,'nonzero_contractions':nonzero,
  'matching':'W=M6 A.A_tilde + M10 B.B/2 + y2 A.(Lambda Lambda)36 + y3 B.(A_tilde Lambda)100 generates W_eff=-(y2*y3)^2 I6(Lambda)/(2*M6^2*M10) in compatible invariant normalizations.',
  'scope':'Renormalizable supersymmetric family messenger sector and leading tree holomorphic matching. Additional allowed self-cubics are included in the audit and affect effective coefficients or higher orders. A complete softly broken scalar vacuum and radiative mixed-operator matching are not derived.'}
 (OUT/'valentiner_messenger.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':census()
