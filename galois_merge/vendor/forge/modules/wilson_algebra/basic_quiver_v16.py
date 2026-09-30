"""Native five-arrow transport ISA for the species-3 Wilson transport algebra.

An amplified element is represented by vertex payloads
  a in k, A in M15(k), S in M5(k)
and arrows
  bp[2] in M_{1x5}(k), Bm[3] in M_{15x5}(k).
The underlying radical-square-zero basic quiver has vertices plus, minus, row
and arrows row->plus (2) and row->minus (3).
"""
from dataclasses import dataclass
import numpy as np

@dataclass
class NativeElement:
    a: object
    A: np.ndarray
    S: np.ndarray
    bp: np.ndarray  # (2,1,5) or (2,5)
    Bm: np.ndarray  # (3,15,5)


def _mod(x,p):
    return np.asarray(x,dtype=np.int64)%p

def _inv_mod(A,p):
    A=_mod(A,p); n=A.shape[0]
    aug=np.c_[A,np.eye(n,dtype=np.int64)]%p
    r=0
    for c in range(n):
        nz=np.flatnonzero(aug[r:,c])
        if len(nz)==0: raise ValueError('singular')
        q=r+int(nz[0])
        if q!=r: aug[[r,q]]=aug[[q,r]]
        z=pow(int(aug[r,c]),p-2,p); aug[r]=aug[r]*z%p
        for i in range(n):
            if i!=r and aug[i,c]: aug[i]=(aug[i]-aug[i,c]*aug[r])%p
        r+=1
    return aug[:,n:]%p

def det_mod(A,p):
    A=_mod(A,p).copy(); n=A.shape[0]; det=1
    for c in range(n):
        nz=np.flatnonzero(A[c:,c])
        if len(nz)==0:return 0
        q=c+int(nz[0])
        if q!=c:
            A[[c,q]]=A[[q,c]]; det=(-det)%p
        piv=int(A[c,c]); det=det*piv%p
        ip=pow(piv,p-2,p); A[c]=A[c]*ip%p
        for i in range(c+1,n):
            if A[i,c]: A[i]=(A[i]-A[i,c]*A[c])%p
    return int(det%p)

def normalize(x,p):
    return NativeElement(int(x.a)%p,_mod(x.A,p),_mod(x.S,p),_mod(x.bp,p).reshape(2,1,5),_mod(x.Bm,p).reshape(3,15,5))

def multiply(x,y,p):
    """Return x*y in ordinary block-matrix order."""
    x=normalize(x,p); y=normalize(y,p)
    bp=np.empty((2,1,5),dtype=np.int64)
    Bm=np.empty((3,15,5),dtype=np.int64)
    for i in range(2): bp[i]=(x.a*y.bp[i] + x.bp[i]@y.S)%p
    for i in range(3): Bm[i]=(x.A@y.Bm[i] + x.Bm[i]@y.S)%p
    return NativeElement(x.a*y.a%p,x.A@y.A%p,x.S@y.S%p,bp,Bm)

def block_matrices(x,p):
    x=normalize(x,p)
    Tp=np.zeros((11,11),dtype=np.int64); Tm=np.zeros((30,30),dtype=np.int64)
    Tp[0,0]=x.a; Tp[0,1:]=np.hstack([x.bp[0].ravel(),x.bp[1].ravel()])
    Tp[1:,1:]=np.kron(np.eye(2,dtype=np.int64),x.S)%p
    Tm[:15,:15]=x.A
    Tm[:15,15:]=np.hstack([x.Bm[0],x.Bm[1],x.Bm[2]])
    Tm[15:,15:]=np.kron(np.eye(3,dtype=np.int64),x.S)%p
    return Tp%p,Tm%p

def divisor(x,p):
    x=normalize(x,p)
    return int((x.a*det_mod(x.A,p)*pow(det_mod(x.S,p),6,p))%p)

def is_unit(x,p):
    return divisor(x,p)!=0

def inverse(x,p):
    x=normalize(x,p)
    if not is_unit(x,p): raise ValueError('nonunit')
    ai=pow(int(x.a),p-2,p); Ai=_inv_mod(x.A,p); Si=_inv_mod(x.S,p)
    bp=np.empty_like(x.bp); Bm=np.empty_like(x.Bm)
    for i in range(2): bp[i]=(-ai*(x.bp[i]@Si))%p
    for i in range(3): Bm[i]=(-((Ai@x.Bm[i])%p@Si))%p
    return NativeElement(ai,Ai,Si,bp,Bm)

def basic_multiply(x,y,p):
    """8D basic algebra coordinates: (alpha,beta,gamma,u1,u2,v1,v2,v3)."""
    x=np.asarray(x,dtype=np.int64)%p; y=np.asarray(y,dtype=np.int64)%p
    a,b,g=x[:3]; ap,bp,gp=y[:3]
    out=np.zeros(8,dtype=np.int64); out[:3]=[a*ap,b*bp,g*gp]
    out[3:5]=(a*y[3:5]+x[3:5]*gp)%p
    out[5:8]=(b*y[5:8]+x[5:8]*gp)%p
    return out%p

def basic_divisor(x,p):
    x=np.asarray(x,dtype=np.int64)%p
    return int(x[0]*x[1]*x[2]%p)
