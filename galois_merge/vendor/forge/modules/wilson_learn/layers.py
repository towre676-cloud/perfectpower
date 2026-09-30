from __future__ import annotations
import numpy as np
import torch
from torch import nn
from pathlib import Path
import sys
HERE=Path(__file__).resolve()
# local import works when repo modules is on PYTHONPATH
from formation_code.core import hamming_manifest

Q192_ROUTES=(49,12,125,48,116,59,95)

class Q192RouteBank(nn.Module):
    """Seven exact Wilson orbital message channels on the labelled Q192 graph."""
    def __init__(self, graph_npz, normalize=True):
        super().__init__(); z=np.load(graph_npz,allow_pickle=False)
        nb=torch.as_tensor(z['neighbors'].astype(np.int64),dtype=torch.long)
        slots=z['slot_frozen_orbital'].astype(np.int64)
        self.routes=Q192_ROUTES; self.normalize=normalize
        for r in self.routes:
            idx=np.flatnonzero(slots==r)
            self.register_buffer(f'n_{r}',nb[:,idx],persistent=False)
    def forward(self,x):
        if x.ndim < 2 or x.shape[0] != 7392: raise ValueError('expected first dimension 7392')
        out=[]
        for r in self.routes:
            n=getattr(self,f'n_{r}')
            z=x[n].sum(dim=1)
            if self.normalize: z=z/n.shape[1]
            out.append(z)
        return torch.stack(out,dim=1) # [V,7,C]

class Q192EquivariantLinear(nn.Module):
    """Exact seven-route equivariant layer plus a self channel."""
    def __init__(self, graph_npz, cin, cout, normalize=True):
        super().__init__(); self.bank=Q192RouteBank(graph_npz,normalize)
        self.weight=nn.Parameter(torch.empty(7,cin,cout)); self.self_weight=nn.Parameter(torch.empty(cin,cout)); self.bias=nn.Parameter(torch.zeros(cout))
        nn.init.xavier_uniform_(self.weight); nn.init.xavier_uniform_(self.self_weight)
    def forward(self,x):
        z=self.bank(x)
        return torch.einsum('vrf,rfo->vo',z,self.weight)+x@self.self_weight+self.bias

class FormationHammingEquivariant(nn.Module):
    """Higher-order equivariant mixture whose admissible route masks are exactly Hamming [7,4,3] codewords.

    Each branch aggregates a permitted codeword support before applying a shared pointwise nonlinearity.
    This preserves M22 permutation equivariance but does not collapse to an unconstrained pairwise mask list.
    """
    def __init__(self, graph_npz, cin, cout, normalize=True, include_zero=False):
        super().__init__(); self.bank=Q192RouteBank(graph_npz,normalize); self.include_zero=include_zero
        man=hamming_manifest(); masks=np.asarray(man['codewords'],dtype=np.float32)
        if not include_zero: masks=masks[masks.sum(1)>0]
        self.register_buffer('masks',torch.tensor(masks,dtype=torch.float32),persistent=True)
        self.logits=nn.Parameter(torch.zeros(len(masks)))
        self.branch_weight=nn.Parameter(torch.empty(cin,cout)); self.self_weight=nn.Parameter(torch.empty(cin,cout)); self.bias=nn.Parameter(torch.zeros(cout))
        nn.init.xavier_uniform_(self.branch_weight); nn.init.xavier_uniform_(self.self_weight)
    def forward(self,x):
        z=self.bank(x) # V,R,C
        denom=self.masks.sum(1).clamp_min(1.0)
        branches=torch.einsum('mr,vrc->mvc',self.masks,z)/denom[:,None,None]
        branches=torch.nn.functional.gelu(torch.einsum('mvc,co->mvo',branches,self.branch_weight)+self.bias)
        alpha=torch.softmax(self.logits,dim=0)
        return torch.einsum('m,mvo->vo',alpha,branches)+x@self.self_weight


class SchurHammingWalshEquivariant(nn.Module):
    """Exact M22 x A equivariant Hamming-Schur sidecar on the Q192 route fabric.

    Input and output are in Schur-frequency coordinates with shape [7392,16,C].
    Each frequency receives an M22-equivariant route filter whose permitted route
    support is the corresponding seven-bit Hamming codeword.  The nonlinearity is
    applied after an orthonormal Walsh transform to the 16 central states and is
    transformed back afterwards.  This is the executable v12 selection-rule bridge:
    pointwise nonlinear fusion in central-state space is equivalent to code-addition
    frequency conservation in Schur space.
    """
    def __init__(self, graph_npz, sidecar_json, cin, cout, normalize=True, activation='gelu'):
        super().__init__(); self.bank=Q192RouteBank(graph_npz,normalize)
        import json
        spec=json.loads(Path(sidecar_json).read_text())
        masks=np.asarray([f['word7'] for f in spec['frequencies']],dtype=np.float64)
        H=np.asarray(spec['walsh_hadamard'],dtype=np.float64)/4.0
        if masks.shape!=(16,7) or H.shape!=(16,16): raise ValueError('bad Hamming sidecar')
        self.register_buffer('masks',torch.tensor(masks,dtype=torch.float64),persistent=True)
        self.register_buffer('walsh',torch.tensor(H,dtype=torch.float64),persistent=True)
        self.route_weight=nn.Parameter(torch.empty(16,7,cin,cout))
        self.self_weight=nn.Parameter(torch.empty(16,cin,cout))
        nn.init.xavier_uniform_(self.route_weight); nn.init.xavier_uniform_(self.self_weight)
        self.activation=activation
    def forward(self,xhat):
        if xhat.ndim!=3 or xhat.shape[0]!=7392 or xhat.shape[1]!=16:
            raise ValueError('expected [7392,16,channels] in Schur-frequency coordinates')
        z=self.bank(xhat) # [V,7,16,C]
        rw=self.route_weight*self.masks[:,:,None,None].to(self.route_weight.dtype)
        y=torch.einsum('vrfc,frco->vfo',z,rw)+torch.einsum('vfc,fco->vfo',xhat,self.self_weight)
        H=self.walsh.to(dtype=y.dtype)
        central=torch.einsum('af,vfo->vao',H.T,y)
        if self.activation=='gelu': central=torch.nn.functional.gelu(central)
        elif self.activation=='tanh': central=torch.tanh(central)
        else: raise ValueError(self.activation)
        return torch.einsum('fa,vao->vfo',H,central)
    def translate_frequency(self,xhat,coord4):
        """Apply a central translation a in F2^4 directly in Fourier coordinates."""
        import itertools
        a=torch.as_tensor(coord4,dtype=torch.long,device=xhat.device)
        if a.numel()!=4: raise ValueError('coord4 must have four bits')
        coords=torch.tensor(list(itertools.product((0,1),repeat=4)),dtype=torch.long,device=xhat.device)
        signs=1-2*((coords*a).sum(1)%2)
        return xhat*signs.to(dtype=xhat.dtype)[None,:,None]
