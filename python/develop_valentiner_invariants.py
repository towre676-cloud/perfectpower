"""Exact low-degree invariant census for the genuine 3.A6 triplet.
No CKM targets enter the invariant or mediator calculations.
"""
from collections import Counter
from fractions import Fraction as F
from pathlib import Path
import json
from math import factorial
import numpy as np
import sympy as s
from sympy.polys.matrices import DomainMatrix
from develop_valentiner_frames import generators, group_closure, product, conjugate

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions'
Z=(F(0),)*4
O=(F(1),F(0),F(0),F(0))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def scale(a,n):return tuple(x*n for x in a)
def exact_integer(a):
    assert a[1:]==Z[1:] and a[0].denominator==1,a
    return int(a[0])
def symchars(t,n):
    # det(1-zg)=1-tr(g)z+conjugate(tr(g))z^2-z^3, since g in SU(3).
    h=[O]
    for k in range(1,n+1):
        v=product(t,h[k-1])
        if k>=2:v=sub(v,product(conjugate(t),h[k-2]))
        if k>=3:v=add(v,h[k-3])
        h.append(v)
    return h

def census(n=12):
    elements,_,_=group_closure(generators())
    traces=Counter(tuple(sum(F(g[1][3*i+i][j],g[0]) for i in range(3)) for j in range(4)) for g in elements)
    chars=[(count,symchars(t,n)) for t,count in traces.items()]
    dims={}
    for p in range(n+1):
        for q in range(n+1-p):
            total=Z
            for count,h in chars:total=add(total,scale(product(h[p],conjugate(h[q])),F(count,1080)))
            dims[f'{p},{q}']=exact_integer(total)
    norms=[]
    for p in range(n+1):
        total=Z
        for count,h in chars:total=add(total,scale(product(h[p],conjugate(h[p])),F(count,1080)))
        norms.append(exact_integer(total))
    return {'group_order':len(elements),'distinct_trace_count':len(traces),'bidegree_dimensions':dims,'symmetric_power_character_norms':norms}

def tensor_census(n=8):
    elements,_,_=group_closure(generators())
    traces=Counter(tuple(sum(F(g[1][3*i+i][j],g[0]) for i in range(3)) for j in range(4)) for g in elements)
    def su3_tensor_parts(k):
        weights=Counter()
        for a in range(k+1):
            for b in range(a+1):
                c=k-a-b
                if not 0<=c<=b:continue
                partition=[a,b,c];hooks=1
                for i,row in enumerate(partition):
                    for j in range(row):hooks*=row-j+sum(partition[r]>j for r in range(i+1,3))
                weights[(a-c,b-c)]+=factorial(k)//hooks
        return weights
    powers=[]
    for t,count in traces.items():
        h=[O]
        for k in range(n):h.append(product(h[-1],t))
        powers.append((count,h))
    results={}
    for p in range(n+1):
        for q in range(n+1-p):
            total=Z
            for count,h in powers:total=add(total,scale(product(h[p],conjugate(h[q])),F(count,1080)))
            group=exact_integer(total)
            up=su3_tensor_parts(p);down=su3_tensor_parts(q)
            continuous=sum(v*down[k] for k,v in up.items())
            results[f'{p},{q}']={'finite':group,'SU3':continuous,'extra':group-continuous}
            if p+q<=5:assert group==continuous
    assert results['6,0']=={'finite':6,'SU3':5,'extra':1}
    assert results['3,3']=={'finite':6,'SU3':6,'extra':0}
    return results

def sextic():
    x=s.symbols('x y z'); w=(-1+s.sqrt(3)*s.I)/2
    K=s.QQ.algebraic_field(s.sqrt(5),w)
    mons=[x[0]**a*x[1]**b*x[2]**(6-a-b) for a in range(7) for b in range(7-a)]
    gs=[]
    for den,es in generators():
        gs.append(s.Matrix(3,3,[(a+b*s.sqrt(5)+(c+d*s.sqrt(5))*w)/den for a,b,c,d in es]))
    def action(g):
        images=list(g*s.Matrix(x))
        cols=[]
        for mon in mons:
            poly=s.Poly(s.expand(mon.xreplace(dict(zip(x,images)))) ,*x)
            cols.append([poly.coeff_monomial(m) for m in mons])
        return s.Matrix.hstack(*map(s.Matrix,cols))
    # Sparse monomial generators first, reducing to a small subspace before h.
    mat=s.Matrix.vstack(*(action(gs[i])-s.eye(28) for i in (0,1,3)))
    basis=DomainMatrix.from_Matrix(mat).convert_to(K).nullspace().to_Matrix().T
    assert basis.cols>0
    remaining=(action(gs[2])-s.eye(28))*basis
    null=DomainMatrix.from_Matrix(remaining).convert_to(K).nullspace().to_Matrix().T
    assert null.cols==1
    v=basis*null[:,0]
    v=s.Matrix([K.to_sympy(K.from_sympy(c/v[next(i for i,c in enumerate(v) if c!=0)])) for c in v])
    # Verify coefficient identities in the number field for all four generators.
    for g in gs:
        for c in (action(g)-s.eye(28))*v:assert K.from_sympy(c)==K.zero
    poly=s.expand(sum(c*m for c,m in zip(v,mons)))
    terms=[{'powers':list(s.Poly(m,*x).monoms()[0]),'coefficient':str(c)} for c,m in zip(v,mons) if c!=0]
    return {'dimension':1,'polynomial':str(poly),'terms':terms,'coefficient_field':'Q(sqrt(5),sqrt(-3))','four_generator_checks':'exact'}

def mediator_checks():
    rng=np.random.default_rng(6631080)
    worst=0.; worst_kernel=0.; errors=[]
    for _ in range(24):
        C=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)); M=1.7;h=.63
        A=C/M;K=np.eye(3)+A.conj().T@A
        vals,vec=np.linalg.eigh(K); ki=(vec/np.sqrt(vals))@vec.conj().T
        light=np.vstack((np.eye(3),-A))@ki
        mass=np.hstack((C,M*np.eye(3)))
        worst_kernel=max(worst_kernel,float(np.max(np.abs(mass@light))))
        assert np.linalg.matrix_rank(mass)==3
        assert np.max(np.abs(light.conj().T@light-np.eye(3)))<1e-12
        Y=-h*A@ki;S=C@C.conj().T
        H=h*h*S@np.linalg.inv(M*M*np.eye(3)+S)
        worst=max(worst,float(np.max(np.abs(Y@Y.conj().T-H))))
        errors.append(float(np.max(np.abs(H@S-S@H))))
    # An allowed quartic orientation operator changes under independent sector rotation.
    a=np.array([1.,0,0]);b=np.array([.6,.8,0]);t=.01
    c=np.cos(t)*b+np.sin(t)*np.array([-.8,.6,0])
    # CP-even real invariant |phi_u^dagger phi_d|^2; no CKM target used.
    return {'scenarios':24,'right_light_kernel_dimension':3,'heavy_rank':3,'maximum_kernel_residual':worst_kernel,'maximum_canonical_identity_residual':worst,'maximum_frame_commutator':max(errors),'allowed_quartic':{'before':float(abs(a@b)**2),'after':float(abs(a@c)**2)},'scope':'Tree matching before electroweak symmetry breaking; finite-v heavy mixing gives EFT corrections.'}

def main():
    result=census();print('exact census complete',flush=True)
    result['tensor_dimensions']=tensor_census();result['sextic']=sextic();print('exact sextic complete',flush=True)
    result['mediator']=mediator_checks()
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/'valentiner_invariants.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
