"""Basis-invariant channel ranks and exact dense schedule costs for the v0.17 five-arrow ISA."""
from __future__ import annotations
import numpy as np
from scripts.lib.modular_exact import rref_mod


def rank_mod(A, p=1000003):
    A=np.asarray(A,dtype=np.int64)%p
    if A.size==0: return 0
    return len(rref_mod(A,p)[1])


def element_channel_ranks(x,p=1000003):
    """Minimal plus/minus arrow counts after independent GL2/GL3 arrow-basis changes."""
    up=np.asarray(x.bp,dtype=np.int64).reshape(2,5)%p
    vm=np.asarray(x.Bm,dtype=np.int64).reshape(3,75)%p
    return rank_mod(up,p),rank_mod(vm,p)


def family_channel_ranks(elements,p=1000003):
    """Minimal common plus/minus channel counts for a whole family after one GL2 x GL3 rebasing."""
    es=list(elements)
    if not es: return (0,0)
    up=np.concatenate([np.asarray(x.bp,dtype=np.int64).reshape(2,5) for x in es],axis=1)%p
    vm=np.concatenate([np.asarray(x.Bm,dtype=np.int64).reshape(3,75) for x in es],axis=1)%p
    return rank_mod(up,p),rank_mod(vm,p)


def schedule_profile(k_plus,k_minus):
    if not (0<=k_plus<=2 and 0<=k_minus<=3): raise ValueError('channel counts outside native ISA')
    vertex=15**3 + 5**3 + 1
    plus_each=5 + 5*5
    minus_each=15*15*5 + 15*5*5
    return {
        'k_plus':int(k_plus),'k_minus':int(k_minus),
        'basic_dimension':3+int(k_plus)+int(k_minus),
        'amplified_dimension':251+5*int(k_plus)+75*int(k_minus),
        'dense_scalar_multiplications':vertex+plus_each*int(k_plus)+minus_each*int(k_minus),
        'dense_vertex_multiplications':vertex,
        'dense_arrow_multiplications':plus_each*int(k_plus)+minus_each*int(k_minus),
    }
