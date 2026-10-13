"""Exact delayed-return identities and additive destruction of the grading."""
import csv, json, math
from collections import deque
import numpy as np
from scipy.linalg import eigh
from research import ROOT, OUT, PRIMES, adjacency, power_mask, iroot, pauli

def write(name,rows):
    with (OUT/name).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)

def neighbors(n,N,add):
    for p in PRIMES:
        if n*p<=N:yield n*p
        if n%p==0:yield n//p
    if add:
        if n>1:yield n-1
        if n<N:yield n+1

def onset(N,values,add):
    best=N+1;pair=None
    for a in values:
        seen={a:0};queue=deque([a])
        while queue:
            x=queue.popleft();dist=seen[x]
            if dist+1>=best:continue
            for y in neighbors(x,N,add):
                if y in seen:continue
                seen[y]=dist+1
                if y in values and y!=a:
                    best=dist+1;pair=(a,y);break
                queue.append(y)
    return (None,None) if pair is None else (best,pair)

def main():
    exact=[];count=0
    # Weighted integer tests of compressed offdiagonal renormalization.
    for N in (64,128,256,512):
        C=adjacency(N,primes=(2,3,5),weights=(1,2,3)).astype(np.int64)
        for d in range(2,7):
            ix=np.flatnonzero(power_mask(N,d));W=np.eye(N,dtype=np.int64)
            for k in range(1,d+1):
                W=W@C;B=W[np.ix_(ix,ix)].copy();np.fill_diagonal(B,0)
                if k<d:assert not B.any()
                else:
                    target=adjacency(iroot(N,d),primes=(2,3,5),weights=(1,2**d,3**d)).astype(np.int64)
                    assert np.array_equal(B,target)
                count+=1
            exact.append(dict(N=N,d=d,population=len(ix),first_possible_order=d,
                nonzero_order_d_entries=int(np.count_nonzero(B)),identity=True))
    write('renormalization.csv',exact)
    rows=[]
    for N in (256,1024,4096,16384):
        for d in range(2,9):
            values=set(np.flatnonzero(power_mask(N,d))+1)
            for add in (False,True):
                first,pair=onset(N,values,add)
                rows.append(dict(N=N,d=d,population=len(values),addition=add,
                    first_return_order=first,start=pair[0] if pair else None,
                    end=pair[1] if pair else None))
    write('shortest_returns.csv',rows)
    # Shifted-power populations: exact BFS on the same arithmetic graph.
    rows=[];N=4096
    for d in (2,3,4,5):
        for shift in range(-12,13):
            values={a**d-shift for a in range(1,iroot(N+max(shift,0),d)+1)
                    if 1<=a**d-shift<=N}
            first,pair=onset(N,values,False)
            rows.append(dict(N=N,d=d,shift=shift,population=len(values),
                first_return_order=first,start=pair[0] if pair else None,end=pair[1] if pair else None))
    write('shifted_returns.csv',rows)
    # Spinor probability: from 1 to 2^d, both final spins summed.
    rows=[]
    for d in range(2,7):
        # A single prime chain avoids exponentially large ambient integer matrices.
        L=2*d+1;C=np.diag(np.ones(L-1),1)+np.diag(np.ones(L-1),-1)
        h=np.arange(L)*math.log(2);P=np.arange(L)%d==0
        for mass in (0.,4.,16.):
            D=pauli(C,h,mass*(~P));ev,V=eigh(D)
            for t in (.003,.01,.03,.1):
                psi=V@(np.exp(-1j*t*ev)*V[0,:].conj())
                prob=float(abs(psi[d])**2+abs(psi[L+d])**2)
                pred=t**(2*d)/math.factorial(d)**2
                # Very small probabilities can fall below eigensolver cancellation.
                rows.append(dict(d=d,mass=mass,t=t,probability=prob,
                    predicted=pred,ratio=prob/pred,reliable_scale=pred>1e-22))
    write('delayed_probabilities.csv',rows)
    (OUT/'selection_receipt.json').write_text(json.dumps(dict(exact_integer_checks=count,
        renormalization_cases=len(exact),shortest_return_cases=56,shifted_cases=100),indent=2))
    print('selection identities and perturbations complete',count,flush=True)

if __name__=='__main__':main()
