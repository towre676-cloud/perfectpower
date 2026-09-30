from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from math import gcd
from typing import Iterable, Sequence, Tuple

Vec=Tuple[int,...]
Mat=Tuple[Tuple[int,...],...]

def _mv(M: Sequence[Sequence[int]], v: Sequence[int], n:int)->Vec:
    return tuple(sum(int(a)*int(b) for a,b in zip(row,v))%n for row in M)

@dataclass(frozen=True)
class SchurSectionRelation:
    """Finite cyclic relation R_n(alpha) = {(x,y): Ux=Vy mod n}.

    U and V represent the two pullback maps into H^2 of the section domain.
    This is an invariant-level compiler object; it does not compute group homology.
    """
    n:int
    U:Mat
    V:Mat
    source_dim:int
    target_dim:int

    def contains(self,x:Sequence[int],y:Sequence[int])->bool:
        if len(x)!=self.source_dim or len(y)!=self.target_dim:
            return False
        return _mv(self.U,x,self.n)==_mv(self.V,y,self.n)

    def pairs(self)->set[tuple[Vec,Vec]]:
        return {(x,y) for x in product(range(self.n),repeat=self.source_dim)
                      for y in product(range(self.n),repeat=self.target_dim)
                      if self.contains(x,y)}

    @staticmethod
    def diagonal_strip(n:int,k:int)->"SchurSectionRelation":
        # y=x_1+...+x_k; equation sum x_i - y = 0.
        return SchurSectionRelation(n,(tuple([1]*k),),((1,),),k,1)


def compose_pairs(a:SchurSectionRelation,b:SchurSectionRelation)->set[tuple[Vec,Vec]]:
    """Relational composite, for small finite compiler/regression instances."""
    if a.n!=b.n or a.target_dim!=b.source_dim: raise ValueError('incompatible relations')
    pa=a.pairs(); pb=b.pairs(); by_mid={}
    for y,z in pb: by_mid.setdefault(y,[]).append(z)
    return {(x,z) for x,y in pa for z in by_mid.get(y,())}

def block_sum(y:Sequence[int], blocks:Sequence[Sequence[int]], n:int)->Vec:
    return tuple(sum(int(y[k]) for k in block)%n for block in blocks)

def cyclic_line_contains(top:Sequence[int],vec:Sequence[int],n:int)->bool:
    return any(tuple((a*t)%n for t in top)==tuple(vec) for a in range(n))

def reservoir_full(y:Sequence[int],block:Sequence[int],n:int)->bool:
    g=n
    for k in block:g=gcd(g,int(y[k]))
    return g==1

def unique_double_witnesses(rel:SchurSectionRelation,omega:Sequence[int],blocks:Sequence[Sequence[int]],top_line:Sequence[int],d_block:Sequence[int],proper_pred=None):
    """Reference witness enumerator for the v16 unique-double criterion."""
    if proper_pred is None: proper_pred=lambda y:True
    ans=[]
    for a in range(rel.n):
        x=tuple((a*z)%rel.n for z in omega)
        for y in product(range(rel.n),repeat=rel.target_dim):
            if not rel.contains(x,y): continue
            bs=block_sum(y,blocks,rel.n)
            if not cyclic_line_contains(top_line,bs,rel.n): continue
            if not reservoir_full(y,d_block,rel.n): continue
            if proper_pred(y): ans.append((a,y,bs))
    return ans
