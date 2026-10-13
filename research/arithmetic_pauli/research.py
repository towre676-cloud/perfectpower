"""Reproducible height/Pauli arithmetic laboratory; no zeta-zero input.

Run: OPENBLAS_NUM_THREADS=1 python research.py --seconds 610
Dependencies: numpy, scipy. Outputs CSV, JSON, and a timed progress log.
"""
from pathlib import Path
import argparse, csv, json, math, time, platform
import numpy as np
from scipy.linalg import eigvalsh, eigh

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'results'
PRIMES=(2,3,5,7)

def iroot(n,d):
    if n<1:return 0
    lo,hi=0,1 << ((n.bit_length()+d-1)//d)
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**d<=n:lo=mid
        else:hi=mid
    return lo

def power_mask(n,d):
    a=np.zeros(n,dtype=bool)
    for k in range(1,iroot(n,d)+1):a[k**d-1]=True
    return a

def masks(n):
    prime=np.ones(n+1,dtype=bool);prime[:2]=False
    for p in range(2,math.isqrt(n)+1):
        if prime[p]:prime[p*p::p]=False
    sf=np.ones(n+1,dtype=bool);sf[0]=False
    for p in range(2,math.isqrt(n)+1):
        if prime[p]:sf[p*p::p*p]=False
    ans={f'power{d}':power_mask(n,d) for d in range(2,7)}
    ans.update(prime=prime[1:],squarefree=sf[1:],mod6_1=(np.arange(1,n+1)%6==1))
    # y^2 = n^2+1 and y^2=2n^2+1; exact integer arithmetic.
    for a in (1,2):
        ans[f'pell{a}']=np.array([math.isqrt(a*k*k+1)**2==a*k*k+1 for k in range(1,n+1)])
    return ans

def adjacency(n,add=0.,primes=PRIMES,weights=None):
    C=np.zeros((n,n));weights=weights or [1.]*len(primes)
    for p,w in zip(primes,weights):
        k=np.arange(1,n//p+1);C[p*k-1,k-1]+=w;C[k-1,p*k-1]+=w
    if add:
        k=np.arange(n-1);C[k,k+1]+=add;C[k+1,k]+=add
    return C

def pauli(C,h,r):
    return np.block([[np.diag(r),C-1j*np.diag(h)],
                     [C+1j*np.diag(h),-np.diag(r)]])

def append(name,row):
    path=OUT/name;exists=path.exists()
    with path.open('a',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(row))
        if not exists:w.writeheader()
        w.writerow(row)

def finite_tests():
    checks=0;maxerr=0.
    rng=np.random.default_rng(271828)
    for n in (8,13,24,37):
        C=adjacency(n,.37);h=np.log(np.arange(1,n+1))
        for d in (2,3,4):
            P=power_mask(n,d).astype(float);Q=1-P;m=1.7
            D=pauli(C,h,m*Q);D0=pauli(C,h,np.zeros(n))
            comm=C*Q[None,:]-Q[:,None]*C
            B=np.sum((C*(Q[:,None]*P[None,:]))**2)
            assert abs(np.sum(comm**2)-2*B)<1e-10;checks+=1
            tr2=np.trace(D@D).real
            expected2=2*(np.sum(C*C)+np.sum(h*h)+m*m*np.sum(Q))
            assert abs(tr2-expected2)<1e-8;checks+=1
            A=C@C+np.diag(h*h)
            expected4=4*m*m*np.sum(np.diag(A)*Q)+2*m**4*np.sum(Q)+2*m*m*np.sum(comm**2)
            actual4=np.trace(np.linalg.matrix_power(D,4)-np.linalg.matrix_power(D0,4)).real
            err=abs(actual4-expected4)/max(1,abs(expected4));maxerr=max(maxerr,err)
            assert err<1e-11;checks+=1
            ev=eigvalsh(D);assert np.max(abs(ev+ev[::-1]))<1e-10;checks+=1
    # Selection-rule tests are exact integer matrix powers, not float eigenvalues.
    for n in (32,81,243):
        C=adjacency(n,primes=(2,3)).astype(np.int64)
        for d in range(2,6):
            ix=np.flatnonzero(power_mask(n,d));W=np.eye(n,dtype=np.int64)
            for k in range(1,d+1):
                W=W@C;compressed=W[np.ix_(ix,ix)].copy();np.fill_diagonal(compressed,0)
                if k<d:assert not np.any(compressed);checks+=1
                else:
                    expected=adjacency(iroot(n,d),primes=(2,3)).astype(np.int64)
                    assert np.array_equal(compressed,expected);checks+=1
    return dict(checks=checks,max_relative_fourth_moment_error=maxerr)

def exact_counts():
    for N in (100,1000,10000,100000,1000000,2000000):
        for d in range(2,9):
            P=power_mask(N,d);root=iroot(N,d)
            for p in (2,3,5,7,11,13):
                k=np.arange(1,N//p+1)
                outgoing=int(np.sum(P[k-1] & ~P[p*k-1]))
                incoming=int(np.sum(~P[k-1] & P[p*k-1]))
                formula=iroot(N//p,d)+root//p
                assert outgoing+incoming==formula
                append('exact_boundaries.csv',dict(N=N,d=d,p=p,population=root,
                    outgoing=outgoing,incoming=incoming,boundary=formula,
                    boundary_per_solution=formula/root,
                    limiting_ratio=p**(-1/d)+1/p))

def spectral_case(n,label,P,add,m,seed=-1):
    h=np.log(np.arange(1,n+1));C=adjacency(n,add);Q=(~P).astype(float)
    D=pauli(C,h,m*Q);ev=eigvalsh(D,overwrite_a=True,check_finite=False)
    B=float(np.sum(C[np.ix_(~P,P)]**2));internal=float(np.sum(C[np.ix_(P,P)]**2)/2)
    epos=ev[n:];gap=float(np.min(abs(ev)))
    append('spectra.csv',dict(n=n,family=label,population=int(P.sum()),add=add,mass=m,seed=seed,
        boundary=B,internal_edges=internal,gap=gap,positive_mean=float(epos.mean()),
        positive_std=float(epos.std()),pair_error=float(np.max(abs(ev+ev[::-1]))),
        moment2=float(np.sum(ev**2)),moment4=float(np.sum(ev**4))))

def effective_case(d,p,m,g=.5):
    # Prime-power chain p^a, a=0..3d; retained sites a=0,d,2d,3d.
    L=3*d+1;C=adjacency(L,primes=()) if False else np.diag(np.ones(L-1),1)+np.diag(np.ones(L-1),-1)
    h=np.arange(L)*math.log(p);P=np.arange(L)%d==0;Q=~P
    A=np.diag(h+m*Q)+g*C
    pp=np.flatnonzero(P);qq=np.flatnonzero(Q);E=h[d]
    # Exact finite Feshbach correction at fixed E; not an eigenvalue approximation.
    X=A[np.ix_(pp,qq)];Z=A[np.ix_(qq,qq)]-E*np.eye(len(qq))
    eff=A[np.ix_(pp,pp)]-X@np.linalg.solve(Z,X.T)
    coupling=float(eff[0,1])
    leading=(-1)**(d-1)*g**d/np.prod(m+h[1:d]-E)
    vals,V=eigh(A)
    low=np.argsort(np.sum(abs(V[P,:])**2,axis=0))[-int(P.sum()):]
    leakage=float(np.max(np.sum(abs(V[Q,:][:,low])**2,axis=0)))
    append('effective_transport.csv',dict(d=d,p=p,mass=m,g=g,coupling=coupling,
        leading=float(leading),relative_error=abs(coupling/leading-1),
        scaled=abs(coupling)*m**(d-1)/g**d,max_selected_leakage=leakage))

def dynamics_case(n,d,add,m):
    P=power_mask(n,d);h=np.log(np.arange(1,n+1));C=adjacency(n,add)
    D=pauli(C,h,m*(~P));vals,V=eigh(D,check_finite=False)
    # start at n=1, upper spin; solution population includes both spin channels.
    start=np.zeros(2*n);start[0]=1;coef=V.conj().T@start
    PP=np.r_[P,P]
    for t in (.001,.003,.01,.03,.1,.3,1.,3.):
        psi=V@(np.exp(-1j*t*vals)*coef)
        loss=float(np.sum(abs(psi[~PP])**2));B=float(np.sum(C[~P,0]**2))
        append('dynamics.csv',dict(n=n,d=d,add=add,mass=m,t=t,leakage=loss,
            t2_prediction=t*t*B,relative_t2_error=abs(loss/(t*t*B)-1),
            norm_error=abs(float(np.vdot(psi,psi).real)-1)))

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--seconds',type=float,default=610.)
    args=parser.parse_args();OUT.mkdir(exist_ok=True)
    for f in OUT.glob('*.csv'):f.unlink()
    t0=time.perf_counter();cpu0=time.process_time()
    tests=finite_tests();print('exact finite tests',tests,flush=True)
    exact_counts();print('large exact boundaries complete',flush=True)
    for d in range(2,9):
        for p in (2,3,5,7):
            for m in (20,40,80,160,320,640,1280):effective_case(d,p,m)
    for d in (2,3,4,5):
        for add in (0.,.25,1.):
            for m in (0.,4.,16.,64.):dynamics_case(96,d,add,m)
    print('effective transport and spinor dynamics complete',flush=True)
    rng=np.random.default_rng(20261013);cases=0;last=time.perf_counter()
    for n in (96,192,320):
        for label,P in masks(n).items():
            for add in (0.,.25,1.):
                for m in (0.,4.,16.):
                    spectral_case(n,label,P,add,m);cases+=1
                    if time.perf_counter()-last>20:
                        print('grid',cases,'elapsed',round(time.perf_counter()-t0,1),flush=True);last=time.perf_counter()
    print('arithmetic spectral grid complete',cases,flush=True)
    ensemble=0
    while time.perf_counter()-t0<args.seconds:
        n=(192,256,320,384)[ensemble%4];d=2+ensemble%5
        target=power_mask(n,d);k=int(target.sum())
        P=np.zeros(n,dtype=bool);P[rng.choice(n,k,replace=False)]=True
        add=(0.,.25,1.)[(ensemble//5)%3];m=(4.,16.)[(ensemble//15)%2]
        spectral_case(n,f'random_matched_power{d}',P,add,m,ensemble)
        ensemble+=1
        if time.perf_counter()-last>20:
            print('matched controls',ensemble,'elapsed',round(time.perf_counter()-t0,1),flush=True);last=time.perf_counter()
    receipt=dict(wall_seconds=time.perf_counter()-t0,cpu_seconds=time.process_time()-cpu0,
        grid_cases=cases,random_control_cases=ensemble,tests=tests,seed=20261013,
        python=platform.python_version(),numpy=np.__version__)
    (OUT/'receipt.json').write_text(json.dumps(receipt,indent=2));print(receipt,flush=True)

if __name__=='__main__':main()
