"""Height-stratified controls and exact mass-moment recovery."""
import time,math,json
import numpy as np
from research import OUT,power_mask,adjacency,pauli,spectral_case,append
from scipy.linalg import eigvalsh

def main():
    rng=np.random.default_rng(314159);t0=time.perf_counter();cases=0
    for n in (192,320,384):
        for d in range(2,7):
            target=power_mask(n,d);ix=np.flatnonzero(target)+1;k=len(ix)
            for add in (0.,.25,1.):
                for mass in (4.,16.):
                    spectral_case(n,'controlled_target_power'+str(d),target,add,mass,-2)
                    for rep in range(8):
                        for typ in ('anchor','height_stratified'):
                            P=np.zeros(n,dtype=bool);P[0]=True
                            if typ=='anchor':
                                if k>1:P[rng.choice(np.arange(1,n),k-1,replace=False)]=True
                            else:
                                # One point in each disjoint geometric-midpoint height bin.
                                cuts=[1]+[max(2,int(math.sqrt(ix[j-1]*ix[j]))) for j in range(1,k)]+[n+1]
                                for j in range(1,k):P[rng.integers(cuts[j],cuts[j+1])-1]=True
                            spectral_case(n,f'{typ}_power{d}',P,add,mass,rep)
                            cases+=1
    # Recover count and boundary from finite spectral moments, with direct identity checks.
    for n in (24,48,96):
        h=np.log(np.arange(1,n+1));C=adjacency(n,.25)
        for d in (2,3,4,5):
            P=power_mask(n,d);Q=(~P).astype(float);m=4.
            v0=eigvalsh(pauli(C,h,np.zeros(n)))
            vm=eigvalsh(pauli(C,h,m*Q))
            q_est=(sum(vm**2)-sum(v0**2))/(2*m*m)
            A=C@C+np.diag(h*h)
            moment_delta=sum(vm**4)-sum(v0**4)
            boundary_est=(moment_delta-4*m*m*np.sum(np.diag(A)*Q)-2*m**4*sum(Q))/(4*m*m)
            boundary=float(np.sum(C[np.ix_(~P,P)]**2))
            append('spectral_recovery.csv',dict(n=n,d=d,count=int(P.sum()),
                recovered_count=n-q_est,count_error=abs(n-q_est-P.sum()),
                boundary=boundary,recovered_boundary=boundary_est,
                boundary_error=abs(boundary_est-boundary)))
    (OUT/'control_receipt.json').write_text(json.dumps(dict(cases=cases,seconds=time.perf_counter()-t0,
        seed=314159,control_definitions='anchor=force 1, otherwise uniform; stratified=force 1, one per log-height bin'),indent=2))
    print('height controls complete',cases,flush=True)

if __name__=='__main__':main()
