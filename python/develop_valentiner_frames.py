"""Exact 3.A6 closure and exhaustive minimal Abelian residual-frame census.

Generators: Hagedorn, Meroni, Vitale, arXiv:1307.5308, equations (7,33).
The group closure is exact in Q(sqrt(5),omega); frame overlaps are numerical.
No nominated CKM coefficient, phase, or mixing anchor enters generation.
"""
from pathlib import Path
from functools import reduce
from math import gcd
from itertools import permutations
import json
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts/m22_interactions'
ZERO = (0,0,0,0)
ONE = (1,0,0,0)


def add(p,q):
    return tuple(a+b for a,b in zip(p,q))


def neg(p):
    return tuple(-a for a in p)


def product(p,q):
    def quadratic(a,b):
        return (a[0]*b[0]+5*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    ac = quadratic(p[:2],q[:2]); bd = quadratic(p[2:],q[2:])
    ad = quadratic(p[:2],q[2:]); bc = quadratic(p[2:],q[:2])
    return (ac[0]-bd[0],ac[1]-bd[1],ad[0]+bc[0]-bd[0],ad[1]+bc[1]-bd[1])


def conjugate(p):
    a,b,c,d = p
    return (a-c,b-d,-c,-d)


def normalize(den,entries):
    g = reduce(gcd,(abs(x) for e in entries for x in e),den)
    return (den//g,tuple(tuple(x//g for x in e) for e in entries))


def mul(a,b):
    da,aa=a;db,bb=b
    entries=[]
    for i in range(3):
        for j in range(3):
            v=ZERO
            for k in range(3):
                v=add(v,product(aa[3*i+k],bb[3*k+j]))
            entries.append(v)
    return normalize(da*db,entries)


def dagger(a):
    den,aa=a
    return (den,tuple(conjugate(aa[3*j+i]) for i in range(3) for j in range(3)))


def matrix(rows,den=1):
    entries=[]
    for row in rows:
        for e in row:
            entries.append((e,0,0,0) if isinstance(e,int) else e)
    return normalize(den,entries)


IDENTITY=matrix([[1,0,0],[0,1,0],[0,0,1]])


def generators():
    a=matrix([[0,1,0],[0,0,1],[1,0,0]])
    f=matrix([[1,0,0],[0,-1,0],[0,0,-1]])
    h=matrix([[-2,(-1,-1,0,0),(-1,1,0,0)],[(-1,-1,0,0),(-1,1,0,0),-2],[(-1,1,0,0),-2,(-1,-1,0,0)]],4)
    q=matrix([[-1,0,0],[0,0,(0,0,-1,0)],[0,(1,0,1,0),0]])
    return [a,f,h,q]


def group_closure(gens):
    elements=[IDENTITY];lookup={IDENTITY:0}; words=['I']
    for i,g in enumerate(elements):
        for n,s in enumerate(gens):
            sg=mul(s,g)
            if sg not in lookup:
                lookup[sg]=len(elements);elements.append(sg);words.append('afhq'[n]+words[i].replace('I',''))
                if len(elements)>1080:
                    raise AssertionError('Unexpected group order')
    return elements,lookup,words


def numeric(g):
    den,aa=g
    w=np.exp(2j*np.pi/3);s=np.sqrt(5)
    return np.array([(a+b*s+(c+d*s)*w)/den for a,b,c,d in aa]).reshape(3,3)


def order(g):
    p=g;n=1
    while p!=IDENTITY:
        p=mul(p,g);n+=1
        assert n<=15
    return n


def determinant(g):
    den,aa=g
    v=ZERO
    for p in permutations(range(3)):
        sign=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
        term=product(product(aa[p[0]],aa[3+p[1]]),aa[6+p[2]])
        v=add(v,term if sign==1 else neg(term))
    assert v==(den**3,0,0,0)


def residual_frames(elements,lookup,words):
    frames={}
    allnumeric=[numeric(g) for g in elements]
    def add_frame(h,source):
        values,u=np.linalg.eigh(h)
        if min(np.diff(values))<1e-8:
            return
        ps=[np.outer(u[:,i],u[:,i].conj()) for i in range(3)]
        def key(p):
            return tuple(np.round(np.concatenate([p.real.ravel(),p.imag.ravel()]),8))
        idx=sorted(range(3),key=lambda i:key(ps[i]))
        k=tuple(key(ps[i]) for i in idx)
        if k not in frames:
            frames[k]={'frame':u[:,idx],'source':source}
    for i,g in enumerate(allnumeric):
        add_frame((g+g.conj().T)/2+.317j*(g-g.conj().T),{'type':'cyclic','element':i,'word':words[i],'order':order(elements[i])})
    cyclic_count=len(frames)
    involutions=[i for i,g in enumerate(elements) if order(g)==2]
    assert len(involutions)==45
    kleins=set()
    for i in involutions:
        for j in involutions:
            if i<j and mul(elements[i],elements[j])==mul(elements[j],elements[i]):
                k=lookup[mul(elements[i],elements[j])]
                kleins.add(tuple(sorted([i,j,k])))
    assert len(kleins)==30
    for i,j,k in sorted(kleins):
        add_frame(allnumeric[i]+.217*allnumeric[j],{'type':'Klein','elements':[i,j,k],'words':[words[x] for x in (i,j,k)]})
    return list(frames.values()),cyclic_count,kleins,involutions,allnumeric


def census(frames,involutions,matrices):
    min_nonzero=1.;max_nonunit=0.;closest=None;best=10.; all_values=set()
    perms=list(permutations(range(3)))
    unitary_residual=0.
    # Comparing to the identity is a structural hierarchy test, not a fit to anchors.
    for i,a in enumerate(frames):
        u=a['frame'];unitary_residual=max(unitary_residual,float(np.max(np.abs(u.conj().T@u-np.eye(3)))))
        for j,b in enumerate(frames):
            v=u.conj().T@b['frame'];p=np.abs(v)**2
            nonzero=np.abs(v)[np.abs(v)>1e-7]
            nonunit=np.abs(v)[np.abs(v)<1-1e-7]
            min_nonzero=min(min_nonzero,float(nonzero.min()))
            max_nonunit=max(max_nonunit,float(nonunit.max(initial=0)))
            all_values.update(float(x) for x in np.round(p.ravel(),10))
            for assignment in perms:
                offdiag=3-sum(p[k,assignment[k]] for k in range(3))
                if offdiag>1e-8 and offdiag<best:
                    best=float(offdiag);closest={'frames':[i,j],'column_assignment':list(assignment),'magnitudes':np.abs(v[:,assignment]).tolist(),'J':float(np.imag(v[0,0]*v[1,1]*v[0,1].conj()*v[1,0].conj()))}
    lines=[]
    for i in involutions:
        eigen,u=np.linalg.eigh(matrices[i]);idx=np.argmax(eigen);lines.append(u[:,idx])
    fixed={float(x) for x in np.round(np.abs(np.array(lines).conj()@np.array(lines).T)**2,10).ravel()}
    return {'minimal_cyclic_frame_count':sum(x['source']['type']=='cyclic' for x in frames),
        'complete_frame_count':len(frames),'ordered_frame_pairs':len(frames)**2,'mass_label_assignments_per_pair':36,
        'total_labeled_pairs':len(frames)**2*36,'minimum_nonzero_magnitude':min_nonzero,'maximum_nonunit_magnitude':max_nonunit,
        'squared_magnitude_spectrum':sorted(all_values),'closest_nontrivial_identity_frame':closest,
        'minimum_total_offdiagonal_probability':best,'frame_unitarity_residual':unitary_residual,
        'involution_fixed_line_squared_overlaps':sorted(fixed),
        'scope':'Complete minimal Abelian frames plus fixed lines for two involution residuals. Floating point overlaps; exact group closure. No breaking corrections included.'}


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    gens=generators()
    for g in gens:
        assert mul(dagger(g),g)==IDENTITY
        determinant(g)
    elements,lookup,words=group_closure(gens)
    assert len(elements)==1080
    assert len(group_closure(gens[:3])[0])==60
    center=[i for i,g in enumerate(elements) if all(mul(g,s)==mul(s,g) for s in gens)]
    assert len(center)==3
    frames,cyclic,kleins,involutions,matrices=residual_frames(elements,lookup,words)
    print('exact group',len(elements),'cyclic frames',cyclic,'complete frames',len(frames),flush=True)
    result=census(frames,involutions,matrices)
    result.update({'group_order':len(elements),'center_order':len(center),'A5_subgroup_order':60,
        'generators_source':'https://arxiv.org/abs/1307.5308 equations (7,33)',
        'field':'Q(sqrt(5),omega), omega^2+omega+1=0','arithmetic':'exact integer numerators and common denominator',
        'residual_frame_sources':[f['source'] for f in frames],
        'generators_exact':[{'denominator':g[0],'entries':g[1]} for g in gens],
        'element_order_histogram':{o:sum(order(g)==o for g in elements) for o in sorted({order(g) for g in elements})}})
    (OUT/'valentiner_frames.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k in ['minimum_nonzero_magnitude','maximum_nonunit_magnitude','involution_fixed_line_squared_overlaps','closest_nontrivial_identity_frame']},indent=2),flush=True)


if __name__=='__main__':
    main()
