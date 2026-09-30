from __future__ import annotations
import numpy as np

def rs_erasure_peel_q192(graph_npz, erased, radius=130, max_rounds=100):
    """Peel erasures on the Q192 bipartite double cover.

    erased[u,s] is the symbol on edge (left u, right neighbors[u,s]).
    A local RS constraint recovers all remaining incident erasures when their count is <= radius.
    Returns the residual mask and a round ledger. This simulates erasure topology only, not symbol arithmetic.
    """
    z=np.load(graph_npz,mmap_mode='r'); nb=z['neighbors']; rev=z['reverse_slot']
    E=np.asarray(erased,dtype=bool).copy()
    if E.shape!=nb.shape: raise ValueError(f'expected erased shape {nb.shape}')
    ledger=[]
    for rnd in range(max_rounds):
        before=int(E.sum())
        if before==0: break
        left=E.sum(axis=1)
        # incoming[v,t] is E[u,s] for u=nb[v,t], s=rev[v,t]
        incoming=E[nb,rev]
        right=incoming.sum(axis=1)
        goodL=(left>0)&(left<=radius); goodR=(right>0)&(right<=radius)
        if np.any(goodL): E[goodL,:]=False
        if np.any(goodR):
            vv,tt=np.nonzero(goodR[:,None] & incoming)
            uu=nb[vv,tt]; ss=rev[vv,tt]; E[uu,ss]=False
        after=int(E.sum()); ledger.append({'round':rnd+1,'before':before,'after':after,'left_decoders':int(goodL.sum()),'right_decoders':int(goodR.sum())})
        if after==before: break
    return E,ledger
