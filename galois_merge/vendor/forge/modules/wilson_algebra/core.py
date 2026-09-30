from __future__ import annotations
import json
from pathlib import Path
import numpy as np

class WilsonAlgebra:
    """Exact coordinate kernel for the 152-dimensional Wilson orbital algebra."""
    def __init__(self, base_npz, relabel_json=None):
        z=np.load(base_npz, allow_pickle=False)
        self.structure=z['structure'].astype(np.int64)
        self.subdegrees=z['subdegrees'].astype(np.int64)
        self.n=7392
        self.dim=152
        self.identity=151
        self.transpose=None
        if relabel_json:
            d=json.loads(Path(relabel_json).read_text())
            self.transpose=np.asarray(d['frozen_transpose'],dtype=np.int64)
    def basis(self,j):
        x=np.zeros(self.dim,dtype=np.int64); x[int(j)]=1; return x
    def multiply(self,a,b):
        a=np.asarray(a); b=np.asarray(b)
        # e_i e_j = sum_k structure[i,j,k] e_k
        return np.einsum('i,j,ijk->k',a,b,self.structure,optimize=True)
    def adjoint(self,a):
        if self.transpose is None: raise ValueError('transpose map not loaded')
        a=np.asarray(a)
        out=np.zeros_like(a)
        out[self.transpose]=a
        return out
    def degree(self,a):
        return int(np.dot(np.asarray(a,dtype=object),self.subdegrees.astype(object)))
    def right_regular(self,a):
        a=np.asarray(a)
        out=np.zeros((self.dim,self.dim),dtype=np.result_type(a,self.structure))
        for j in np.flatnonzero(a): out += a[j]*self.structure[:,j,:]
        return out
    def left_regular(self,a):
        a=np.asarray(a)
        out=np.zeros((self.dim,self.dim),dtype=np.result_type(a,self.structure))
        for i in np.flatnonzero(a): out += a[i]*self.structure[i,:,:]
        return out
    @staticmethod
    def rank_mod(A,p):
        A=np.asarray(A,dtype=np.int64).copy()%p; m,n=A.shape; r=0
        for c in range(n):
            piv=np.flatnonzero(A[r:,c])
            if not len(piv): continue
            i=r+int(piv[0]); A[[r,i]]=A[[i,r]]
            A[r]=(A[r]*pow(int(A[r,c]),-1,p))%p
            nz=np.flatnonzero(A[:,c]); nz=nz[nz!=r]
            for q in nz: A[q]=(A[q]-A[q,c]*A[r])%p
            r+=1
            if r==m: break
        return r
    def closure_growth(self, generators, p=1000003, max_degree=12):
        """Cumulative right-word span dimensions; full 152 proves Q-generation."""
        gens=[np.asarray(g,dtype=np.int64)%p for g in generators]
        mats=[]
        for g in gens:
            M=np.zeros((152,152),dtype=np.int64)
            for j in np.flatnonzero(g): M=(M+int(g[j])*self.structure[:,j,:])%p
            mats.append(M)
        rows=[]; pivs=[]
        def add(v):
            nonlocal rows,pivs
            v=np.asarray(v,dtype=np.int64).copy()%p
            for row,k in zip(rows,pivs):
                if v[k]: v=(v-v[k]*row)%p
            nz=np.flatnonzero(v)
            if not len(nz): return False
            k=int(nz[0]); v=(v*pow(int(v[k]),-1,p))%p
            pos=int(np.searchsorted(pivs,k)); pivs.insert(pos,k); rows.insert(pos,v)
            for q in range(pos+1,len(rows)):
                if rows[q][k]: rows[q]=(rows[q]-rows[q][k]*v)%p
            return True
        I=self.basis(self.identity)%p; add(I); front=[I]; growth=[1]
        for _deg in range(1,max_degree+1):
            nf=[]
            for v in front:
                for M in mats:
                    w=v@M%p; nf.append(w); add(w)
            front=nf; growth.append(len(rows))
            if len(rows)==152: break
        return growth

class LabelledOrbitalAction:
    """Exact 7392-state relation labelling. Reference execution path for 152-parameter layers."""
    def __init__(self, relation_npz):
        self.relation=np.load(relation_npz, mmap_mode='r')['relation']
        self.n=self.relation.shape[0]
    def apply_scalar(self, coeff, x, chunk_rows=32):
        coeff=np.asarray(coeff)
        x=np.asarray(x)
        if x.shape[0]!=self.n: raise ValueError('x first dimension must be 7392')
        tail=x.shape[1:]
        xf=x.reshape(self.n,-1)
        y=np.empty_like(xf,dtype=np.result_type(coeff,x))
        for a in range(0,self.n,chunk_rows):
            b=min(self.n,a+chunk_rows)
            # Dense reference: A[v,w]=coeff[relation[v,w]].
            W=coeff[self.relation[a:b]]
            y[a:b]=W@xf
        return y.reshape((self.n,)+tail)
