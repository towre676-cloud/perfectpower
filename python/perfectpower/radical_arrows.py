"""Basic three-vertex, five-arrow radical-square-zero Wilson algebra.

A generic recovered algebra model, not the original 152-dimensional carrier.
"""
from dataclasses import dataclass
from fractions import Fraction as Q

# Two arrows 2→0 and three arrows 2→1. Matrix-block convention: target on left.
ENDS=((2,0),(2,0),(2,1),(2,1),(2,1))

@dataclass(frozen=True)
class ArrowElement:
    diagonal:tuple
    arrows:tuple

    def __post_init__(self):
        object.__setattr__(self,'diagonal',tuple(self.diagonal))
        object.__setattr__(self,'arrows',tuple(self.arrows))
        if len(self.diagonal)!=3 or len(self.arrows)!=5 or any(type(x) not in (int,Q) for x in self.diagonal+self.arrows):
            raise ValueError('three exact diagonal entries and five exact arrows required')
        object.__setattr__(self,'diagonal',tuple(map(Q,self.diagonal)))
        object.__setattr__(self,'arrows',tuple(map(Q,self.arrows)))

    def __add__(self,other):
        return ArrowElement(tuple(a+b for a,b in zip(self.diagonal,other.diagonal)),tuple(a+b for a,b in zip(self.arrows,other.arrows)))

    def __mul__(self,other):
        return ArrowElement(tuple(a*b for a,b in zip(self.diagonal,other.diagonal)),
                            tuple(self.diagonal[t]*y+x*other.diagonal[s]
                                  for x,y,(s,t) in zip(self.arrows,other.arrows,ENDS)))

    def inverse(self):
        if any(x==0 for x in self.diagonal):raise ValueError('nonunit diagonal')
        inv=tuple(1/x for x in self.diagonal)
        return ArrowElement(inv,tuple(-x*inv[t]*inv[s] for x,(s,t) in zip(self.arrows,ENDS)))

    def regular_matrix(self):
        basis=[ArrowElement(tuple(int(i==j) for i in range(3)),(0,)*5) for j in range(3)]
        basis += [ArrowElement((0,)*3,tuple(int(i==j) for i in range(5))) for j in range(5)]
        cols=[(self*b).diagonal+(self*b).arrows for b in basis]
        return tuple(zip(*cols))

    def carrier_matrix(self):
        """Faithful scalar block carrier a ⊕ A ⊕ S^6, including shared S.

        This representation's determinant is a A S^6. The left regular
        representation has different multiplicities: a^3 A^4 S.
        """
        a,b,c=self.diagonal;out=[[Q(0)]*8 for _ in range(8)]
        for i,value in enumerate((a,b,c,c,c,c,c,c)):out[i][i]=value
        for value,(row,col) in zip(self.arrows,((0,2),(0,3),(1,4),(1,5),(1,6))):out[row][col]=value
        return tuple(tuple(row) for row in out)

ONE=ArrowElement((1,1,1),(0,)*5)
ZERO=ArrowElement((0,)*3,(0,)*5)
