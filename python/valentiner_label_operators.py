"""Closed contractions for a triangle of three bifundamental source fields."""
from itertools import product,combinations_with_replacement
from functools import lru_cache
import numpy as np
from valentiner_rank_lifting import unpack,trace
from valentiner_joint import Jet,link_poly

EDGES={(0,1):'L',(1,0):'l',(0,2):'A',(2,0):'a',(1,2):'B',(2,1):'b'}
DAG={k:v for k,v in zip('LlAaBb','lLaAbB')}


def canonical(word):
    variants=[word[i:]+word[:i] for i in range(len(word))]
    return min(variants)


def conjugated(word):return canonical(''.join(DAG[t] for t in word[::-1]))


@lru_cache(None)
def patterns():
    cycles={}
    for n in range(2,7):
        for vs in product(range(3),repeat=n):
            pairs=list(zip(vs,vs[1:]+vs[:1]))
            if any(a==b for a,b in pairs):continue
            w=canonical(''.join(EDGES[p] for p in pairs));cycles[w]=(w.count('A')-w.count('a'),w.count('B')-w.count('b'))
    cs=sorted(cycles,key=lambda t:(len(t),t));rows=set()
    for count in range(1,4):
        for words in combinations_with_replacement(cs,count):
            degree=sum(map(len,words))
            if degree>6:continue
            charge=tuple(sum(cycles[w][i] for w in words)%6 for i in range(2))
            if charge!=(0,0):continue
            adj=tuple(sorted([conjugated(w) for w in words],key=lambda t:(len(t),t)))
            rows.add(min(words,adj))
    return sorted(rows,key=lambda q:(sum(map(len,q)),q))


def trace_candidates(x,derivatives=False,exact=False):
    L,A,B=unpack(x)
    if derivatives:
        z=np.concatenate([L.ravel(),A.ravel(),B.ravel()]);jets=[]
        for i,v in enumerate(z):
            g=np.zeros(54,complex);g[i]=1;g[i+27]=1j;jets.append(Jet(v,g))
        L,A,B=[np.array(jets[i:i+9],object).reshape(3,3) for i in [0,9,18]]
    M={'L':L,'l':L.conj().T,'A':A,'a':A.conj().T,'B':B,'b':B.conj().T};cache={};rows=[]
    def tr(w):
        if w not in cache:
            value=M[w[0]]
            for t in w[1:]:value=value@M[t]
            cache[w]=trace(value)
        return cache[w]
    for words in patterns():
        value=1
        for w in words:value=value*tr(w)
        rows.append((sum(map(len,words)),'*'.join('Tr('+w+')' for w in words),value.real))
    if derivatives:return [d for d,n,v in rows],[n for d,n,v in rows],np.array([v.v.real for d,n,v in rows]),np.array([v.g.real for d,n,v in rows])
    return [d for d,n,v in rows],[n for d,n,v in rows],np.array([v if exact else float(v) for d,n,v in rows],dtype=object if exact else float)
