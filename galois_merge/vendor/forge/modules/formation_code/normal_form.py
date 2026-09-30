#!/usr/bin/env python3
"""Finite F2 bookkeeping for the v13 mixed central normal form.
This is a regression/sidecar utility, not a proof of the group-theoretic theorems.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, List, Sequence, Tuple


def xor_basis(rows: Iterable[int]) -> List[int]:
    """Reduced XOR basis, highest pivot first."""
    b = {}
    for x in sorted(set(int(v) for v in rows), reverse=True):
        while x:
            p = x.bit_length() - 1
            if p in b:
                x ^= b[p]
            else:
                b[p] = x
                for q in list(b):
                    if q != p and ((b[q] >> p) & 1):
                        b[q] ^= x
                break
    return [b[p] for p in sorted(b, reverse=True)]


def span(rows: Iterable[int]) -> List[int]:
    basis = xor_basis(rows)
    vals = [0]
    for b in basis:
        vals += [x ^ b for x in vals]
    return sorted(set(vals))


def bits(x: int, n: int) -> Tuple[int, ...]:
    return tuple((x >> j) & 1 for j in range(n))


def block_offsets(block_sizes: Sequence[int]) -> List[Tuple[int, int]]:
    out=[]; s=0
    for n in block_sizes:
        out.append((s,s+n)); s += n
    return out


def parity_projection(x: int, block_sizes: Sequence[int]) -> int:
    y=0
    for i,(a,b) in enumerate(block_offsets(block_sizes)):
        parity=0
        for j in range(a,b): parity ^= (x >> j) & 1
        y |= parity << i
    return y


def activity_support(rows: Iterable[int], block_sizes: Sequence[int]) -> int:
    a=0
    basis=xor_basis(rows)
    for i,(lo,hi) in enumerate(block_offsets(block_sizes)):
        mask=((1 << (hi-lo))-1) << lo
        if any(x & mask for x in basis): a |= 1 << i
    return a

@dataclass(frozen=True)
class Shadow:
    species_support: int
    central_activity: int
    parity_basis: Tuple[int, ...]

    def parity_span(self) -> Tuple[int, ...]:
        return tuple(span(self.parity_basis))


def shadow(block_sizes: Sequence[int], dual_rows: Iterable[int]) -> Shadow:
    r=len(block_sizes)
    species=0
    for i,n in enumerate(block_sizes):
        if n: species |= 1 << i
    db=xor_basis(dual_rows)
    act=activity_support(db, block_sizes)
    pb=xor_basis(parity_projection(x, block_sizes) for x in db)
    return Shadow(species, act, tuple(pb))


def join(shadows: Sequence[Shadow]) -> Shadow:
    s=a=0; rows=[]
    for sh in shadows:
        s |= sh.species_support
        a |= sh.central_activity
        rows.extend(sh.parity_basis)
    return Shadow(s,a,tuple(xor_basis(rows)))


def leq(x: Shadow, y: Shadow) -> bool:
    if x.species_support & ~y.species_support: return False
    if x.central_activity & ~y.central_activity: return False
    ys=set(span(y.parity_basis))
    return all(c in ys for c in span(x.parity_basis))


def amalgam_shadow(m: Sequence[int]) -> Shadow:
    total=sum(m)
    if total == 0: return Shadow(0,0,())
    allones=(1 << total)-1
    return shadow(m,[allones])


def critical_prediction(m: Sequence[int]) -> bool:
    supp=[x for x in m if x>0]
    if not supp: return False
    if len(supp)==1:
        return supp[0] in (1,2)
    return all(x==1 for x in supp)


def fmtmask(x:int,r:int)->str:
    return ''.join(str((x>>i)&1) for i in range(r))

if __name__ == '__main__':
    examples=[(1,), (2,), (3,), (1,1), (2,1), (2,2), (1,1,1), (3,2,1)]
    for m in examples:
        sh=amalgam_shadow(m)
        print(m, 'S='+fmtmask(sh.species_support,len(m)),
              'A='+fmtmask(sh.central_activity,len(m)),
              'C_basis='+str([fmtmask(c,len(m)) for c in sh.parity_basis]),
              'critical='+str(critical_prediction(m)))
