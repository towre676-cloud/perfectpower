from __future__ import annotations
import json, math
from pathlib import Path
from typing import Any
import numpy as np

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'DATA/RELATION/TASK_MULTI_EXCHANGE_V25'
V23=ROOT/'DATA/RELATION/TASK_SELECTED_WORD_PROGRAMS_V23'
WORDS=json.loads((ROOT/'DATA/RELATION/INTEGRAL_NATIVE_ISA_V21/word_names_v21.json').read_text())
PRIMES=(1_000_003,1_000_033,1_000_037,1_000_039,1_000_081)
GENERATOR_COST={'G':1732,'H':1689}
PLUS=(np.arange(251,256),np.arange(256,261))
MINUS=(np.arange(261,336),np.arange(336,411),np.arange(411,486))
PROGRAM_FILES=('sensor_d8_m12_two_exchange.json','paley_d8_m12_two_exchange.json')

def load_program(name:str)->dict[str,Any]:
    if name not in PROGRAM_FILES: raise KeyError(name)
    return json.loads((DATA/name).read_text())

def target_vector(task:str)->np.ndarray:
    t=np.zeros(152,dtype=object)
    if task=='sensor': t[12]=1;t[48]=1
    elif task=='paley':
        for j,s in ((12,-1),(125,1),(48,-1),(116,1),(59,-1),(95,1)):t[j]=s
    else: raise KeyError(task)
    return t

def allowed_indices(mask:str)->np.ndarray:
    if mask=='m12': return np.r_[MINUS[0],MINUS[1]]
    if mask=='p1': return PLUS[0]
    raise KeyError(mask)

def exact_verify(name:str)->dict[str,Any]:
    p=load_program(name)
    mats=np.load(V23/'exact_prefix_1023.npz',allow_pickle=True)
    pos={w:i for i,w in enumerate(WORDS)}
    inds=[pos[w] for w in p['support_words']]
    nums=np.asarray([int(x) for x in p['numerators']],dtype=object); den=int(p['denominator'])
    hv=mats['hecke'][inds].T@nums
    nv=mats['native'][inds].T@nums
    allowed=allowed_indices(p['mask']); keep=np.zeros(486,dtype=bool);keep[allowed]=True
    return {
        'hecke_exact':bool(np.array_equal(hv,target_vector(p['task'])*den)),
        'native_mask_exact':bool(all(int(x)==0 for x in nv[~keep])),
        'allowed_native_nonzero_coordinates':int(sum(int(x)!=0 for x in nv[keep])),
        'support_count':len(inds),
        'height_bits':max(den.bit_length(),max(abs(int(x)).bit_length() for x in nums)),
    }

def _words_len(k:int)->list[str]:
    if k==0:return ['']
    return [''.join('G' if x=='0' else 'H' for x in format(i,f'0{k}b')) for i in range(2**k)]

def _suffixes(m:int)->list[str]:
    out=[]
    for k in range(m+1):out+=_words_len(k)
    return out

def _greedy_independent_rows(A:np.ndarray,p:int)->list[int]:
    A=np.asarray(A,dtype=np.int64)%int(p); piv=[];basis=[];inds=[]
    for i in range(A.shape[0]):
        v=A[i].copy()
        for pc,b in zip(piv,basis):
            if v[pc]:v=(v-int(v[pc])*b)%p
        nz=np.flatnonzero(v)
        if not len(nz):continue
        pc=int(nz[0]);v=v*pow(int(v[pc]),-1,p)%p
        for j,b in enumerate(basis):
            if b[pc]:basis[j]=(b-int(b[pc])*v)%p
        pos=sum(q<pc for q in piv);piv.insert(pos,pc);basis.insert(pos,v);inds.insert(pos,i)
    return inds

def _rank_rows(A:np.ndarray,p:int)->int:
    return len(_greedy_independent_rows(A,p)) if len(A) else 0

def residual_profile_mod(name:str,p:int)->dict[str,Any]:
    d=load_program(name); D=int(d['degree']); den=int(d['denominator'])%p; inv=pow(den,-1,p)
    coeff={w[::-1]:(int(n)%p)*inv%p for w,n in zip(d['support_words'],d['numerators'])}
    bases=[];mats=[];state=[]
    for k in range(D+1):
        P=_words_len(k);S=_suffixes(D-k)
        M=np.asarray([[coeff.get(u+v,0) for v in S] for u in P],dtype=np.int64)
        inds=_greedy_independent_rows(M,p);bases.append([P[i] for i in inds]);mats.append((P,M));state.append(len(inds))
    trans=[]
    for k in range(D):
        Pn,Mn=mats[k+1]; idx={u:i for i,u in enumerate(Pn)}; row=[]
        for sym in 'GH':
            row.append(_rank_rows(np.asarray([Mn[idx[u+sym]] for u in bases[k]],dtype=np.int64),p))
        trans.append(row)
    return {'state_dims':state,'transition_ranks':trans,'primitive_calls':sum(sum(x) for x in trans)}

def global_support_theorem()->dict[str,Any]:
    return json.loads((DATA/'global_81_call_support_theorem.json').read_text())

def matching_preclusion_thresholds()->list[int]:
    return [max(2**k,2**(8-k)-1) for k in range(8)]

def v41_pareto()->dict[str,Any]:
    return json.loads((DATA/'formation_v41_joined_pareto.json').read_text())
