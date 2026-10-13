"""Exact height-barrier populations in valuation coordinates.

The Lean module proves enumeration semantics for the corresponding recurrence.
The iterative Python backend is cross-checked independently, not verified Lean.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import comb, isqrt
import argparse
import json
import random

def _prime(n):
    return isinstance(n,int) and not isinstance(n,bool) and n>=2 and all(n%k for k in range(2,isqrt(n)+1))

def _parameters(p,q,d):
    if not isinstance(d,int) or isinstance(d,bool) or not 0<=d<=4096:
        raise ValueError('exponent must be an integer in 0..4096')
    if not 2<=p<q<=100000 or not _prime(p) or not _prime(q):
        raise ValueError('two increasing primes at most 100000 are required')

def height_ballot(p:int,q:int,d:int):
    """Exact shortest p^d→q^d paths below q^d; O(d²) cells, O(d) integers."""
    _parameters(p,q,d)
    powers=[p**u for u in range(d+1)]
    prev=[0]*(d+1);prev[0]=1
    for v in range(1,d+1):
        threshold=q**v;lo,hi=0,d+1
        while lo+1<hi:
            mid=(lo+hi)//2
            if powers[mid]<=threshold:lo=mid
            else:hi=mid
        row=[0]*(d+1);row[0]=1
        for u in range(1,lo+1):row[u]=row[u-1]+prev[u]
        prev=row
    count=prev[d];total=comb(2*d,d)
    return {'schema':'pp-height-ballot/1','p':p,'q':q,'exponent':d,
            'height_cutoff':q**d,'shortest_length':2*d,'count':count,
            'unrestricted_count':total,'retained_numerator':count,
            'retained_denominator':total,'retained_fraction':float(Fraction(count,total)),
            'scope':'Exact finite path population; Python iterative backend; generic recurrence semantics proved in Lean.'}

def path_population(p,q,u,v):
    """Independent explicit enumeration for small rectangles, in forward order."""
    if min(u,v)<0 or u+v>20:raise ValueError('explicit enumeration supports at most 20 steps')
    def visit(a,b,word):
        if p**a>q**b:return []
        if a==u and b==v:return [word]
        return ((visit(a+1,b,word+(True,)) if a<u else [])+
                (visit(a,b+1,word+(False,)) if b<v else []))
    return visit(0,0,())

class BallotPopulation:
    """Queryable complete path population; True=×p, False=÷q in reversed walk.

    The suffix table gives conditional counts, exact ranks, inverse ranks, and
    seeded uniform sampling without constructing or traversing all paths.
    """
    def __init__(self,p,q,d):
        _parameters(p,q,d)
        if d>256:raise ValueError('queryable path tables support exponents through 256')
        self.p,self.q,self.d=p,q,d
        self.P=[p**u for u in range(d+1)];self.Q=[q**v for v in range(d+1)]
        self.suffix=[[0]*(d+1) for _ in range(d+1)]
        for u in range(d,-1,-1):
            for v in range(d,-1,-1):
                if self.P[u]>self.Q[v]:continue
                self.suffix[u][v]=1 if u==v==d else ((self.suffix[u+1][v] if u<d else 0)+(self.suffix[u][v+1] if v<d else 0))
        self.count=self.suffix[0][0]

    def conditional_count(self,prefix=()):
        u=v=0
        for bit in prefix:
            if type(bit) is not bool:raise ValueError('path symbols must be Boolean')
            u+=bit;v+=not bit
            if u>self.d or v>self.d or self.P[u]>self.Q[v]:return 0
        return self.suffix[u][v]

    def unrank(self,index):
        if type(index) is not int or not 0<=index<self.count:raise ValueError('rank outside the complete population')
        u=v=0;word=[]
        while u<self.d or v<self.d:
            up=self.suffix[u+1][v] if u<self.d else 0
            if index<up:u+=1;word.append(True)
            else:index-=up;v+=1;word.append(False)
        return tuple(word)

    def rank(self,word):
        word=tuple(word)
        if len(word)!=2*self.d or self.conditional_count(word)!=1:raise ValueError('not an admissible complete path')
        u=v=index=0
        for bit in word:
            if bit:u+=1
            else:
                index+=self.suffix[u+1][v] if u<self.d else 0;v+=1
        return index

    def sample(self,seed=0):
        return self.unrank(random.Random(seed).randrange(self.count))

def boundary_count(N,d,primes=(2,3,5,7)):
    if N<1 or d<2:raise ValueError('positive cutoff and exponent at least two required')
    def root(n):
        lo,hi=0,1 << ((n.bit_length()+d-1)//d)
        while lo+1<hi:
            m=(lo+hi)//2
            if m**d<=n:lo=m
            else:hi=m
        return lo
    a=root(N)
    return {'population':a,'boundary':sum(root(N//p)+a//p for p in primes),
            'per_prime':{str(p):root(N//p)+a//p for p in primes}}

def main():
    p=argparse.ArgumentParser(description='Count exact prime paths under a height ceiling')
    p.add_argument('--p',type=int,default=2);p.add_argument('--q',type=int,default=3)
    p.add_argument('--exponent',type=int,default=32)
    p.add_argument('--rank',type=int,help='Retrieve this exact zero-based path rank')
    p.add_argument('--samples',type=int,default=0,help='Number of seeded uniform paths')
    p.add_argument('--seed',type=int,default=0)
    args=p.parse_args();result=height_ballot(args.p,args.q,args.exponent)
    if args.rank is not None or args.samples:
        population=BallotPopulation(args.p,args.q,args.exponent)
        if args.rank is not None:result['ranked_path']=population.unrank(args.rank)
        if not 0<=args.samples<=100:raise ValueError('sample count must be in 0..100')
        rng=random.Random(args.seed)
        result['sample_paths']=[population.unrank(rng.randrange(population.count)) for _ in range(args.samples)]
    print(json.dumps(result))

if __name__=='__main__':main()
