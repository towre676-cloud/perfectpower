from __future__ import annotations
from dataclasses import dataclass
from pathlib import Path
import itertools
import numpy as np

@dataclass(frozen=True)
class MaskResult:
    plus: tuple[int,...]
    minus: tuple[int,...]
    native_dim: int
    signature_rank: int
    signature_kernel_dim: int
    task_dim: int
    task_signature_rank: int
    task_signature_kernel_dim: int
    reachable: bool
    faithful: bool
    arrow_cost: int

class TaskSignatureCompiler:
    """Exact good-prime degree-8 task-section compiler for the v0.21 synchronized fiber product."""
    def __init__(self, root: Path, prime: int = 1000003):
        self.root=Path(root); self.p=int(prime)
        z=np.load(self.root/'DATA/RELATION/INTEGRAL_NATIVE_ISA_V21/integral_native_isa_v21.npz')
        self.NA=z['native_signature'].astype(np.int64)%self.p
        self.NH=z['hecke_signature_aligned'].astype(np.int64)%self.p
        I=np.eye(486,dtype=np.int64)
        self.plus=[I[251:256],I[256:261]]
        self.minus=[I[261:336],I[336:411],I[411:486]]
        self.plus_sig=[x@self.NA.T%self.p for x in self.plus]
        self.minus_sig=[x@self.NA.T%self.p for x in self.minus]
    def rank(self,A):
        A=np.asarray(A,dtype=np.int64)%self.p
        if A.size==0:return 0
        A=A.copy();m,n=A.shape;r=0
        for c in range(n):
            nz=np.flatnonzero(A[r:,c])
            if not len(nz):continue
            q=r+int(nz[0])
            if q!=r:A[[r,q]]=A[[q,r]]
            A[r]=A[r]*pow(int(A[r,c]),self.p-2,self.p)%self.p
            rows=np.flatnonzero(A[:,c]);rows=rows[rows!=r]
            if len(rows):A[rows]=(A[rows]-A[rows,c,None]*A[r])%self.p
            r+=1
            if r==m:break
        return r
    def contains(self,B,T):
        B=np.asarray(B,dtype=np.int64)%self.p;T=np.asarray(T,dtype=np.int64)%self.p
        return self.rank(B)==self.rank(np.vstack([B,T]))
    def task_signature(self,T):
        return np.asarray(T,dtype=np.int64)%self.p @ self.NH.T % self.p
    def mask_rows(self,plus=(),minus=()):
        blocks=[self.plus[j] for j in plus]+[self.minus[j] for j in minus]
        return np.vstack(blocks)%self.p if blocks else np.zeros((0,486),dtype=np.int64)
    def evaluate(self,T,plus=(),minus=()):
        T=np.asarray(T,dtype=np.int64)%self.p
        S=self.mask_rows(plus,minus); G=S@self.NA.T%self.p; F=self.task_signature(T)
        td=self.rank(T);tr=self.rank(F);sr=self.rank(G);sd=len(S)
        reach=self.contains(G,F)
        faithful=bool(reach and (sd-sr)>=td-tr and sd>=td)
        return MaskResult(tuple(j+1 for j in plus),tuple(j+1 for j in minus),sd,sr,sd-sr,td,tr,td-tr,reach,faithful,30*len(plus)+1500*len(minus))
    def all_masks(self,T):
        out=[]
        for rp in range(3):
            for kp in itertools.combinations(range(2),rp):
                for rm in range(4):
                    for km in itertools.combinations(range(3),rm):
                        out.append(self.evaluate(T,kp,km))
        return out
    def optima(self,T):
        ok=[r for r in self.all_masks(T) if r.faithful]
        if not ok:return {}
        return {
            'min_channels':min(ok,key=lambda r:(len(r.plus)+len(r.minus),r.arrow_cost,r.native_dim)),
            'min_native_dim':min(ok,key=lambda r:(r.native_dim,r.arrow_cost,len(r.plus)+len(r.minus))),
            'min_arrow_cost':min(ok,key=lambda r:(r.arrow_cost,r.native_dim,len(r.plus)+len(r.minus))),
        }
    def geometry(self):
        R=self.rank
        P=self.plus_sig;M=self.minus_sig
        pair_minus=[]
        for i,j in itertools.combinations(range(3),2):
            s=R(np.vstack([M[i],M[j]])); pair_minus.append({'pair':[i+1,j+1],'sum_rank':s,'intersection_dim':R(M[i])+R(M[j])-s})
        plus_minus=[]
        for i in range(2):
            for j in range(3):
                s=R(np.vstack([P[i],M[j]])); plus_minus.append({'plus':i+1,'minus':j+1,'sum_rank':s,'intersection_dim':R(P[i])+R(M[j])-s})
        # triple intersection via orthogonal-complement sum
        def nullrows(A):
            A=np.asarray(A,dtype=np.int64)%self.p; m,n=A.shape; Rm=A.copy();r=0;piv=[]
            for c in range(n):
                nz=np.flatnonzero(Rm[r:,c])
                if not len(nz):continue
                q=r+int(nz[0]);Rm[[r,q]]=Rm[[q,r]]
                Rm[r]=Rm[r]*pow(int(Rm[r,c]),self.p-2,self.p)%self.p
                rows=np.flatnonzero(Rm[:,c]);rows=rows[rows!=r]
                if len(rows):Rm[rows]=(Rm[rows]-Rm[rows,c,None]*Rm[r])%self.p
                piv.append(c);r+=1
                if r==m:break
            free=[c for c in range(n) if c not in set(piv)];N=np.zeros((len(free),n),dtype=np.int64)
            for ii,f in enumerate(free):
                N[ii,f]=1
                for rr,c in enumerate(piv):N[ii,c]=(-Rm[rr,f])%self.p
            return N
        perps=[nullrows(x) for x in M]
        triple_inter=127-R(np.vstack(perps))
        return {
            'plus_ranks':[R(x) for x in P],
            'plus_pair_sum_rank':R(np.vstack(P)),
            'plus_pair_intersection_dim':sum(R(x) for x in P)-R(np.vstack(P)),
            'minus_ranks':[R(x) for x in M],
            'minus_pairs':pair_minus,
            'minus_triple_sum_rank':R(np.vstack(M)),
            'minus_triple_intersection_dim':triple_inter,
            'plus_minus_pairs':plus_minus,
        }
