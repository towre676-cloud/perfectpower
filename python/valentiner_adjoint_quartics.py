"""Multiplicity-free Valentiner adjoint quartics and their CP pairing."""
from itertools import combinations_with_replacement
from pathlib import Path
import json
import numpy as np
import sympy as s
from develop_valentiner_frames import generators,group_closure,numeric

ROOT=Path(__file__).resolve().parents[1]
PAIRS=list(combinations_with_replacement(range(8),2))


def hermitian_basis():
    out=[]
    for i in range(3):
        for j in range(i+1,3):
            a=np.zeros((3,3),complex);a[i,j]=a[j,i]=1/np.sqrt(2);out.append(a)
            a=np.zeros((3,3),complex);a[i,j]=-1j/np.sqrt(2);a[j,i]=1j/np.sqrt(2);out.append(a)
    out.extend([np.diag([1,-1,0])/np.sqrt(2),np.diag([1,1,-2])/np.sqrt(6)])
    return np.array(out)


BASIS=hermitian_basis()
EMBED=np.zeros((36,8,8))
for k,(i,j) in enumerate(PAIRS):
    EMBED[k,i,j]=1 if i==j else 1/np.sqrt(2)
    if i!=j:EMBED[k,j,i]=1/np.sqrt(2)


def adjoint(G):
    return np.einsum('aij,jk,bkl,il->ab',BASIS,G,BASIS,G.conj()).real


def symmetric_square(D):return np.einsum('aij,ik,jl,bkl->ab',EMBED,D,D,EMBED,optimize=True)


def quartic_projectors(seed=20261006):
    group=group_closure(generators())[0];reps=[symmetric_square(adjoint(numeric(g))) for g in group]
    rng=np.random.default_rng(seed);a=rng.normal(size=(36,36));a=(a+a.T)/2
    average=sum((D@a@D.T for D in reps),np.zeros((36,36)))/len(reps)
    vals,U=np.linalg.eigh((average+average.T)/2);blocks=[]
    for k,x in enumerate(vals):
        if not blocks or abs(x-vals[blocks[-1][-1]])>1e-8:blocks.append([k])
        else:blocks[-1].append(k)
    P=[U[:,idx]@U[:,idx].T for idx in blocks];ranks=[len(idx) for idx in blocks]
    assert sorted(ranks)==[1,5,5,8,8,9],ranks
    cp=json.loads((ROOT/'receipts/m22_interactions/valentiner_cp.json').read_text())
    X=np.array([[complex(s.sympify(t).evalf()) for t in row] for row in cp['unitary_CP_matrix']])
    C=np.einsum('aij,jk,bkl,il->ab',BASIS,X,BASIS.conj(),X.conj()).real;CP=symmetric_square(C)
    perm=[int(np.argmin([np.linalg.norm(CP@p@CP.T-q) for q in P])) for p in P]
    assert sorted(perm)==list(range(6))
    orbits=[]
    for k in range(6):
        if any(k in o for o in orbits):continue
        orbits.append(sorted({k,perm[k]}))
    even=[sum((P[k] for k in o),np.zeros((36,36))) for o in orbits]
    # Identify the SU(3) adjoint by the anticommutator map, rather than an
    # arbitrary numerical eigenvalue or basis in a multiplicity space.
    dmap=np.einsum('aij,bjk,cki,nbc->an',BASIS,BASIS,BASIS,EMBED).real
    padj=dmap.T@np.linalg.inv(dmap@dmap.T)@dmap
    eranks=[round(np.trace(p)) for p in even]
    singlet=next(p for p,r in zip(even,eranks) if r==1)
    adj_index=int(np.argmin([np.linalg.norm(p-padj) for p in even]))
    extra=next(p for k,(p,r) in enumerate(zip(even,eranks)) if r==8 and k!=adj_index)
    ordered=[singlet,even[adj_index],extra,next(p for p,r in zip(even,eranks) if r==9),next(p for p,r in zip(even,eranks) if r==10)]
    even=ordered
    return even,{'complex_quartic_channels':ranks,'CP_channel_permutation':perm,'CP_even_channel_ranks':[round(np.trace(p)) for p in even],
                 'canonical_CP_even_channels':['singlet_1','SU3_adjoint_8','finite_adjoint_8','finite_9','CP_pair_5_plus_5'],
                 'SU3_adjoint_identification_error':float(np.linalg.norm(even[1]-padj)),
                 'max_generator_invariance_error':float(max(np.linalg.norm(symmetric_square(adjoint(numeric(g)))@p@symmetric_square(adjoint(numeric(g))).T-p) for p in P for g in generators())),
                 'max_CP_even_invariance_error':float(max(np.linalg.norm(CP@p@CP.T-p) for p in even)),
                 'idempotence_error':float(max(np.linalg.norm(p@p-p) for p in even))}


def symmetric_vector(sv):return np.einsum('aij,i,j->a',EMBED,sv,sv)


def quartic_value_gradient(sv,projectors,coefficients):
    w=symmetric_vector(sv);J=2*np.einsum('aij,j->ai',EMBED,sv)
    Pw=sum((c*(P@w) for c,P in zip(coefficients,projectors)),np.zeros(36,complex))
    return float(np.vdot(w,Pw).real),J.T@Pw.conj()


def CP_odd_projector(seed=20261006):
    """The unique mixed CP-odd quartic channel, with deterministic sign."""
    group=group_closure(generators())[0];reps=[symmetric_square(adjoint(numeric(g))) for g in group]
    rng=np.random.default_rng(seed);a=rng.normal(size=(36,36));a=(a+a.T)/2
    average=sum((D@a@D.T for D in reps),np.zeros((36,36)))/len(reps)
    vals,U=np.linalg.eigh((average+average.T)/2);blocks=[]
    for k,x in enumerate(vals):
        if not blocks or abs(x-vals[blocks[-1][-1]])>1e-8:blocks.append([k])
        else:blocks[-1].append(k)
    five=[U[:,idx]@U[:,idx].T for idx in blocks if len(idx)==5];assert len(five)==2
    P=five[0]-five[1]
    first=next(v for v in P.ravel() if abs(v)>1e-9)
    return P if first>0 else -P
