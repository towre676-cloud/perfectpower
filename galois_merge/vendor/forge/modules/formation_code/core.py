from __future__ import annotations
import itertools
import numpy as np

def rref_gf2(A):
    A=np.asarray(A,dtype=np.uint8).copy()&1; m,n=A.shape; piv=[]; r=0
    for c in range(n):
        q=np.flatnonzero(A[r:,c])
        if not len(q): continue
        i=r+int(q[0]); A[[r,i]]=A[[i,r]]
        for j in range(m):
            if j!=r and A[j,c]: A[j]^=A[r]
        piv.append(c); r+=1
        if r==m: break
    return A,piv

def row_basis(A):
    R,p=rref_gf2(A)
    return R[:len(p)]

def nullspace_gf2(A):
    R,piv=rref_gf2(A); n=R.shape[1]; free=[j for j in range(n) if j not in piv]
    out=[]
    for f in free:
        x=np.zeros(n,dtype=np.uint8); x[f]=1
        for i,p in reversed(list(enumerate(piv))):
            x[p]=np.dot(R[i],x)&1
        out.append(x)
    return np.asarray(out,dtype=np.uint8) if out else np.zeros((0,n),dtype=np.uint8)

def orthogonal_complement(G):
    return nullspace_gf2(row_basis(G))

def codewords(G):
    G=row_basis(G); k=G.shape[0]
    return np.asarray([(np.asarray(bits,dtype=np.uint8)@G)&1 for bits in itertools.product([0,1], repeat=k)],dtype=np.uint8)

def contains(G,v):
    B=row_basis(G); return len(row_basis(np.vstack([B,np.asarray(v,dtype=np.uint8)])))==len(B)

def hamming_7_4_generator():
    # Nullspace of parity-check matrix whose columns are all nonzero F2^3 vectors.
    H=np.array([[1,0,1,0,1,0,1],
                [0,1,1,0,0,1,1],
                [0,0,0,1,1,1,1]],dtype=np.uint8)
    G=nullspace_gf2(H)
    assert G.shape==(4,7)
    return G

def hamming_manifest():
    G=hamming_7_4_generator(); C=codewords(G); N=orthogonal_complement(G)
    weights=[int(x.sum()) for x in C]
    return {
      'generator':G.tolist(),'orthogonal_kernel_N':N.tolist(),
      'codewords':C.tolist(),
      'weight_distribution':{str(w):weights.count(w) for w in sorted(set(weights))},
      'minimum_weight':min(w for w in weights if w),
      'weight_three_supports':[np.flatnonzero(x).tolist() for x in C if int(x.sum())==3]
    }
