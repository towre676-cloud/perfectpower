"""Exact geodesic path counts under arithmetic height barriers."""
from functools import lru_cache
import math,json
from research import OUT,append

def factor(n):
    r={};p=2
    while p*p<=n:
        while n%p==0:r[p]=r.get(p,0)+1;n//=p
        p+=1
    if n>1:r[n]=r.get(n,0)+1
    return r

def count(a,b,d,N):
    va,vb=factor(a),factor(b);primes=sorted(set(va)|set(vb))
    steps=tuple(d*abs(vb.get(p,0)-va.get(p,0)) for p in primes)
    signs=tuple(1 if vb.get(p,0)>va.get(p,0) else -1 for p in primes)
    states=0
    @lru_cache(None)
    def f(done):
        nonlocal states;states+=1;n=a**d
        for p,s,k in zip(primes,signs,done):
            if s>0:n*=p**k
            else:n//=p**k
        if n>N:return 0
        if done==steps:return 1
        return sum(f(done[:i]+(done[i]+1,)+done[i+1:])
                   for i in range(len(primes)) if done[i]<steps[i])
    value=f(tuple(0 for _ in primes))
    unbounded=math.factorial(sum(steps))
    for k in steps:unbounded//=math.factorial(k)
    return value,unbounded,states,sum(steps)

def main():
    cases=0
    for a,b in ((2,3),(4,9),(6,10),(12,18),(8,9),(10,21),(30,42)):
        for d in range(1,33):
            for typ in ('tight','lcm'):
                N=(max(a,b) if typ=='tight' else math.lcm(a,b))**d
                value,unbounded,states,length=count(a,b,d,N)
                if typ=='lcm':assert value==unbounded
                assert value>0
                append('height_geodesics.csv',dict(a=a,b=b,d=d,cutoff=typ,N=N,
                    length=length,geodesics=value,unbounded_geodesics=unbounded,
                    retained_fraction=value/unbounded,dp_states=states))
                cases+=1
    (OUT/'geodesic_receipt.json').write_text(json.dumps(dict(exact_cases=cases,
        unrestricted_multinomial_checks=cases//2,arbitrary_precision=True),indent=2))
    print('height-barrier geodesics complete',cases,flush=True)

if __name__=='__main__':main()
