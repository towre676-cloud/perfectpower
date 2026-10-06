"""Actual canonical connection spectra and a conditional three-mode global mass.
The modified flat connection and component selection explicitly break M22.
"""
from pathlib import Path
from collections import deque
import json
import numpy as np
import sympy as s
from flint import fmpz_mat
from develop_m22_transport import small_mul,small_inv,parity,wedge
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/m22_interactions'

def rho(p):
    m=s.Matrix([[int(p[j]==i)-int(p[4]==i) for j in range(4)] for i in range(4)])
    return np.array(wedge(m),dtype=float)

def main():
    r=json.loads((OUT/'cap_transport.json').read_text());vs=sorted(r['component_vertices']);index={v:i for i,v in enumerate(vs)}
    edges={(e['source'],e['target']):tuple(e['permutation']) for e in r['transport_edges']}
    G=np.array(wedge(s.Matrix(r['fiber']['hyperplane_metric'])),dtype=float)
    C=np.linalg.cholesky(G).T;Ci=np.linalg.inv(C)
    units={edge:C@rho(p)@Ci for edge,p in edges.items()}
    lap=6*np.eye(252);adj=s.zeros(42)
    for (a,b),t in units.items():
        ia,ib=index[a],index[b];lap[6*ib:6*ib+6,6*ia:6*ia+6]=-t
        adj[ib,ia]=1
    assert np.max(abs(lap-lap.T))<1e-12
    integer_lap=6*np.eye(252,dtype=int)
    for (a,b),permutation in edges.items():
        integer_lap[6*index[b]:6*index[b]+6,6*index[a]:6*index[a]+6]=-rho(permutation).astype(int)
    factors=fmpz_mat(integer_lap.tolist()).charpoly().factor()[1]
    exact_factors=[{'ascending_coefficients':[int(x) for x in poly],'multiplicity':int(mult)} for poly,mult in factors]
    assert all(len(f['ascending_coefficients'])==2 for f in exact_factors)
    levels=[-F['ascending_coefficients'][0]/F['ascending_coefficients'][1] for F in exact_factors]
    assert min(levels)==2 and max(levels)==10
    vals=np.linalg.eigvalsh(lap);cover=np.sort(np.r_[vals,12-vals])
    assert vals.min()>1e-6 and cover.min()>1e-6
    # Parallel sections are exactly the holonomy-fixed vectors. The stored S5
    # and A5 holonomy act without a trivial summand on wedge^2 standard R4.
    pchar=adj.charpoly().as_expr();t=s.symbols('lambda')
    assert s.expand(pchar-(t-6)*(t-2)**21*(t+1)**6*(t+3)**14)==0
    parallel={vs[0]:tuple(range(5))};queue=[vs[0]]
    for v in queue:
        for w in sorted(b for a,b in edges if a==v):
            if w not in parallel:parallel[w]=small_mul(edges[v,w],parallel[v]);queue.append(w)
    Rs={v:C@rho(p)@Ci for v,p in parallel.items()}
    omega=np.array(r['fiber']['hodge_star_times_sqrt5'],dtype=float)/np.sqrt(5)
    J=C@omega@Ci;assert np.max(abs(J-J.T))<1e-12
    P=(np.eye(6)+J)/2
    # Gauge-trivialized connection; original tree edges remain unchanged.
    flat=6*np.eye(252);penalty=np.zeros((252,252));changed=0
    for (a,b),original in units.items():
        transport=Rs[b]@Rs[a].T
        changed+=int(np.max(abs(transport-original))>1e-8)
        flat[6*index[b]:6*index[b]+6,6*index[a]:6*index[a]+6]=-transport
    for v in vs:
        q=Rs[v]@P@Rs[v].T;ii=index[v]
        penalty[6*ii:6*ii+6,6*ii:6*ii+6]=np.eye(6)-q
    selected=flat+.5*penalty;ev=np.linalg.eigvalsh(selected)
    expected=np.sort(np.r_[np.repeat([0.,4.,7.,9.],[3,63,18,42]),np.repeat([.5,4.5,7.5,9.5],[3,63,18,42])])
    assert np.max(abs(ev-expected))<2e-13
    _,b=np.linalg.eigh(P);basis=b[:,-3:]
    light=np.vstack([Rs[v]@basis for v in vs])/np.sqrt(42)
    assert np.max(abs(light.T@light-np.eye(3)))<1e-13
    assert np.max(abs(selected@light))<1e-13
    # A selector gaps every other cap fiber; no enormous dense matrix is needed.
    total=r['cap_count']*6;outside=(r['cap_count']-42)*6
    spectrum=[{'mass_squared':x,'multiplicity':n} for x,n in [(0,3),(.5,3),(2,outside),(4,63),(4.5,63),(7,18),(7.5,18),(9,42),(9.5,42)]]
    assert sum(t['multiplicity'] for t in spectrum)==total
    result={'canonical_base_dimension':252,'canonical_cover_dimension':504,
        'canonical_base_zero_modes':0,'canonical_cover_zero_modes':0,
        'canonical_connection_characteristic_factors':exact_factors,'canonical_base_gap_exact':2,'canonical_cover_gap_exact':2,'canonical_base_gap_numerical':float(vals.min()),'canonical_cover_gap_numerical':float(cover.min()),
        'scalar_component_adjacency_characteristic_polynomial':'(t-6)(t-2)^21(t+1)^6(t+3)^14',
        'flat_modified_directed_edges':changed,'total_directed_edges':252,
        'selected_component_cap_count':42,'global_cap_count':r['cap_count'],'global_fiber_dimension':6,
        'global_total_modes':total,'global_zero_modes':3,'global_squared_mass_gap':.5,'global_squared_mass_spectrum':spectrum,
        'light_normalization_residual':float(np.max(abs(light.T@light-np.eye(3)))),
        'light_mass_residual':float(np.max(abs(selected@light))),
        'scope':'Canonical connection has no parallel light vectors. Three global wavefunctions require an explicitly modified flat connection and a selected component. This positive Hermitian flavor mass-squared operator is not a derived gauge-invariant chiral quark UV completion.'}
    (OUT/'m22_global_modes.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
