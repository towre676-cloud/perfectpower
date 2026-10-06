"""Exact anti-linear triplet action and complete outer-class inversion audit."""
from pathlib import Path
import json
import numpy as np
import sympy as s
from sympy.polys.matrices import DomainMatrix
from develop_valentiner_frames import generators,group_closure,mul,dagger,conjugate,IDENTITY,numeric
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions'

def compose(*gs):
 r=IDENTITY
 for g in gs:r=mul(r,g)
 return r

def outer_maps(gs):
 a,f,h,q=gs;a2=mul(a,a)
 return [gs,[compose(a,h,q),compose(f,a,h,f),q,compose(a2,h)],
         [compose(a2,h,q),compose(f,a2,h,f),q,compose(a,h)]]

def as_sympy(g):
 w=(-1+s.sqrt(3)*s.I)/2
 return s.Matrix(3,3,[(a+b*s.sqrt(5)+(c+d*s.sqrt(5))*w)/g[0] for a,b,c,d in g[1]])


def sextic_identity(field,U,scalar):
    data=json.loads((OUT/'valentiner_invariants.json').read_text())['sextic']['terms']
    polynomial={tuple(t['powers']):field.from_sympy(s.sympify(t['coefficient'])) for t in data}
    entries=[[field.from_sympy(U[i,j]) for j in range(3)] for i in range(3)]
    def pmul(a,b):
        result={}
        for p,c in a.items():
            for q,d in b.items():
                powers=tuple(x+y for x,y in zip(p,q));result[powers]=result.get(powers,field.zero)+c*d
        return result
    transformed={}
    for powers,coefficient in polynomial.items():
        term={(0,0,0):coefficient}
        for i,n in enumerate(powers):
            linear={tuple(int(j==k) for j in range(3)):entries[i][k] for k in range(3)}
            for _ in range(n):term=pmul(term,linear)
        for powers,c in term.items():transformed[powers]=transformed.get(powers,field.zero)+c
    for powers,c in transformed.items():
        expected=field.from_sympy(scalar**3*s.conjugate(field.to_sympy(polynomial.get(powers,field.zero))))
        assert c==expected
    return len(transformed)

def audit():
 gs=generators();elements,lookup,words=group_closure(gs)
 # Third outer representative from the composition of the first two, not a guessed formula.
 candidate=outer_maps(gs)[:3]
 def mapped(img):
  result=[None]*len(elements);result[0]=IDENTITY
  for i,g in enumerate(elements):
   for r,t in zip(gs,img):
    j=lookup[mul(r,g)];v=mul(t,result[i])
    if result[j] is None:result[j]=v
    else:assert result[j]==v
  return [lookup[x] for x in result]
 maps=[mapped(img) for img in candidate]
 maps.append([maps[1][maps[2][i]] for i in range(1080)])
 assert len(set(tuple(m) for m in maps))==4
 classes=[];indices={}
 for i in range(1080):
  if i in indices:continue
  block={i};queue=[i]
  for j in queue:
   for g in gs:
    k=lookup[compose(g,elements[j],dagger(g))]
    if k not in block:block.add(k);queue.append(k)
  for j in block:indices[j]=len(classes)
  classes.append(sorted(block))
 assert len(classes)==17
 cp=[]
 for m in maps:
  images=[indices[m[c[0]]] for c in classes]
  inv=[indices[lookup[dagger(elements[c[0]])]] for c in classes]
  bad=[i for i in range(17) if images[i]!=inv[i]]
  cp.append({'class_permutation':images,'inverse_class_permutation':inv,'failed_inverse_classes':bad,'class_inverting':not bad})
 assert all(not r['class_inverting'] for r in cp)
 # Solve the R -> Rbar automorphism intertwiner over the exact coefficient field.
 field=s.QQ.algebraic_field(s.sqrt(5),s.sqrt(3)*s.I)
 eq=[]
 for g,image in zip(gs,candidate[2]):
  a=as_sympy(g).conjugate();b=as_sympy(image)
  eq.append(s.kronecker_product(s.eye(3),a.T)-s.kronecker_product(b,s.eye(3)))
 ns=DomainMatrix.from_Matrix(s.Matrix.vstack(*eq)).convert_to(field).nullspace().to_Matrix()
 assert ns.rows==1
 U=s.Matrix(3,3,list(ns[0,:]));first=next(x for x in U if x!=0)
 U=U.applyfunc(lambda x:field.to_sympy(field.from_sympy(x/first)))
 scalar=field.to_sympy(field.from_sympy((U.conjugate().T*U)[0,0]))
 def zero(M):return all(field.from_sympy(x)==field.zero for x in M)
 assert zero(U.conjugate().T*U-scalar*s.eye(3))
 # The published representative may square to an inner automorphism.
 # Compose with an inner action to obtain an involution on elementary triplets.
 un=np.array(U.evalf(),dtype=complex)/np.sqrt(float(scalar))
 candidates=[i for i,g in enumerate(elements) if np.max(abs((numeric(g)@un)@(numeric(g)@un).conj()-np.eye(3)))<1e-10]
 assert candidates
 inner=candidates[0];inner_matrix=as_sympy(elements[inner]);U=inner_matrix*U
 U=U.applyfunc(lambda x:field.to_sympy(field.from_sympy(x)))
 candidate[2]=[compose(elements[inner],g,dagger(elements[inner])) for g in candidate[2]]
 assert zero(U*U.conjugate()-scalar*s.eye(3))
 for g,image in zip(gs,candidate[2]):assert zero(U*as_sympy(g).conjugate()-as_sympy(image)*U)
 checks_count=sextic_identity(field,U,scalar)
 unitary=U/s.sqrt(scalar)
 result={'group_order':1080,'conjugacy_classes':17,'outer_class_representatives':cp,'all_representatives_fail_class_inversion':True,
         'unnormalized_intertwiner':[[str(x) for x in row] for row in U.tolist()],
         'inner_adjustment_element':inner,'inner_adjustment_word':words[inner],'normalization_squared':str(scalar),'unitary_CP_matrix':[[str(s.simplify(x)) for x in row] for row in unitary.tolist()],
         'sextic_CP_identity':'F6(X conjugate(phi))=conjugate(F6(phi))','exact_sextic_coefficient_checks':checks_count,'CP_square_identity':True,'exact_generator_checks':4,
         'scope':'Consistent anti-linear involution on the specified triplet/singlet field content. Not a class-inverting CP action valid for arbitrary irreducible field content.',
         'sources':['https://arxiv.org/abs/1307.5308 equation (34)','https://arxiv.org/abs/1402.0507']}
 OUT.mkdir(parents=True,exist_ok=True);(OUT/'valentiner_cp.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result,indent=2),flush=True)
 return unitary
if __name__=='__main__':audit()
