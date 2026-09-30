from __future__ import annotations
import json
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'DATA/RELATION/TASK_DESIGNED_WORD_PROGRAMS_V24'
V23=ROOT/'DATA/RELATION/TASK_SELECTED_WORD_PROGRAMS_V23'
GENERATOR_COST={'G':1732,'H':1689}
PLUS=(np.arange(251,256),np.arange(256,261))
MINUS=(np.arange(261,336),np.arange(336,411),np.arange(411,486))
SELECTED=('sensor_d8_m12_balanced.json','sensor_d8_m12_height_local.json','paley_d8_m12_balanced.json','sensor_d9_p1_balanced.json','paley_d9_p1_balanced.json')
def load_selected(name):
    if name not in SELECTED: raise KeyError(name)
    return json.loads((DATA/name).read_text())
def target(task):
    t=np.zeros(152,dtype=object)
    if task=='sensor': t[12]=1;t[48]=1
    elif task=='paley':
        for j,s in ((12,-1),(125,1),(48,-1),(116,1),(59,-1),(95,1)): t[j]=s
    else: raise KeyError(task)
    return t
def allowed(degree,mask):
    if degree==8 and mask=='m12': return np.r_[MINUS[0],MINUS[1]]
    if degree==9 and mask=='p1': return PLUS[0]
    raise ValueError((degree,mask))
def exact_verify(name):
    p=load_selected(name); mats=np.load(V23/'exact_prefix_1023.npz',allow_pickle=True)
    names=json.loads((ROOT/'DATA/RELATION/INTEGRAL_NATIVE_ISA_V21/word_names_v21.json').read_text())
    pos={w:i for i,w in enumerate(names)}
    inds=[pos[w] for w in p['support_words']]
    nums=np.asarray([int(x) for x in p['numerators']],dtype=object); den=int(p['denominator'])
    wn=mats['native'][inds]; wh=mats['hecke'][inds]
    hv=wh.T@nums; nv=wn.T@nums
    a=allowed(int(p['degree']),p['mask']); outside=np.ones(486,dtype=bool);outside[a]=False
    return {'hecke_exact':bool(np.array_equal(hv,target(p['task'])*den)),'native_mask_exact':bool(all(int(x)==0 for x in nv[outside])),'support':len(inds),'height_bits':max(den.bit_length(),max(abs(int(x)).bit_length() for x in nums))}
def _matching_bound(edges):
    left=list(dict.fromkeys(a for a,b in edges)); right=list(dict.fromkeys(b for a,b in edges))
    rid={b:i for i,b in enumerate(right)}; adj={a:[] for a in left}
    for a,b in edges: adj[a].append(rid[b])
    mate=[None]*len(right)
    def dfs(a,seen):
        for v in adj[a]:
            if v in seen: continue
            seen.add(v)
            if mate[v] is None or dfs(mate[v],seen): mate[v]=a; return True
        return False
    return sum(dfs(a,set()) for a in left)

def support_upper(words):
    # words are written algebra words; column execution reverses them.
    ew=[w[::-1] for w in words]; d=max(map(len,ew)) if ew else 0
    state=[]; trans=[]
    for k in range(d+1):
        edges=[(w[:k],w[k:]) for w in ew]
        state.append(min(2**k,_matching_bound(edges)))
    for k in range(d):
        row=[]
        for sym in 'GH':
            edges=[(w[:k],w[k+1:]) for w in ew if len(w)>k and w[k]==sym]
            row.append(_matching_bound(edges))
        trans.append(row)
    return {'state_dims':state,'transition_upper_bounds':trans,'primitive_call_upper_bound':sum(sum(x) for x in trans)}
