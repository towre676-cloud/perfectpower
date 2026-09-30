from __future__ import annotations
import json
from pathlib import Path
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'DATA/RELATION/DUAL_HANKEL_SEMANTICS_V26/dual_hankel_profiles.json'
PRIMES=(1000003,1000033,1000037,1000039,1000081)
COST={'G':1732,'H':1689}

def words_len(k):
    if k==0:return ['']
    return [''.join('G' if x=='0' else 'H' for x in format(i,f'0{k}b')) for i in range(2**k)]
def bfs_words(D):
    return sum((words_len(k) for k in range(D+1)),[])
def suffixes(m):
    return sum((words_len(k) for k in range(m+1)),[])
def greedy_rank_rows(A,p):
    A=np.asarray(A,dtype=np.int64)%p
    piv=[]; bas=[]
    for row in A:
        v=row.copy()
        for pc,b in zip(piv,bas):
            if v[pc]: v=(v-int(v[pc])*b)%p
        nz=np.flatnonzero(v)
        if not len(nz): continue
        pc=int(nz[0]); v=v*pow(int(v[pc]),-1,p)%p
        for j,b in enumerate(bas):
            if b[pc]: bas[j]=(b-int(b[pc])*v)%p
        pos=sum(q<pc for q in piv); piv.insert(pos,pc); bas.insert(pos,v)
    return len(piv)
def profile(words,nums,D,p,reverse=False):
    coeff={((w[::-1] if reverse else w)): int(c)%p for w,c in zip(words,nums)}
    state=[]; bases=[]; mats=[]
    for k in range(D+1):
        P=words_len(k); S=suffixes(D-k)
        M=np.asarray([[coeff.get(u+v,0) for v in S] for u in P],dtype=np.int64)
        # get deterministic independent row indices
        A=M%p; piv=[]; bas=[]; inds=[]
        for i,row in enumerate(A):
            v=row.copy()
            for pc,b in zip(piv,bas):
                if v[pc]: v=(v-int(v[pc])*b)%p
            nz=np.flatnonzero(v)
            if not len(nz): continue
            pc=int(nz[0]); v=v*pow(int(v[pc]),-1,p)%p
            for j,b in enumerate(bas):
                if b[pc]: bas[j]=(b-int(b[pc])*v)%p
            pos=sum(q<pc for q in piv); piv.insert(pos,pc); bas.insert(pos,v); inds.insert(pos,i)
        bases.append([P[i] for i in inds]); mats.append((P,M)); state.append(len(inds))
    trans=[]
    for k in range(D):
        Pnext,Mnext=mats[k+1]; idx={u:i for i,u in enumerate(Pnext)}; rr=[]
        for sym in 'GH': rr.append(greedy_rank_rows([Mnext[idx[u+sym]] for u in bases[k]],p))
        trans.append(rr)
    gc=sum(x[0] for x in trans); hc=sum(x[1] for x in trans)
    return {'state_dims':state,'transition_ranks':trans,'G_calls':gc,'H_calls':hc,'primitive_calls':gc+hc,'primitive_cost':gc*COST['G']+hc*COST['H']}

def load_program(path,D,selected=False):
    d=json.loads(path.read_text())
    nums=[int(x) for x in d['numerators']]
    if 'support_words' in d: words=d['support_words']
    else: words=bfs_words(D)[:len(nums)]
    return d,words,nums

specs={
 'sensor_d8_v23':(ROOT/'DATA/RELATION/TASK_SELECTED_WORD_PROGRAMS_V23/sensor_d8_m12_padic.json',8),
 'paley_d8_v23':(ROOT/'DATA/RELATION/TASK_SELECTED_WORD_PROGRAMS_V23/paley_d8_m12_padic.json',8),
 'sensor_d9_v23':(ROOT/'DATA/RELATION/TASK_SELECTED_WORD_PROGRAMS_V23/sensor_d9_p1_padic.json',9),
 'paley_d9_v23':(ROOT/'DATA/RELATION/TASK_SELECTED_WORD_PROGRAMS_V23/paley_d9_p1_padic.json',9),
 'sensor_d8_v25':(ROOT/'DATA/RELATION/TASK_MULTI_EXCHANGE_V25/sensor_d8_m12_two_exchange.json',8),
 'paley_d8_v25':(ROOT/'DATA/RELATION/TASK_MULTI_EXCHANGE_V25/paley_d8_m12_two_exchange.json',8),
}
out={'release':'v0.26.0','semantics':{
 'algebra_build':'left-to-right written-word residual machine; append G/H on the right of the formal algebra word',
 'column_execution':'column vectors evaluate a written product right-to-left; equivalently reverse each written word before residual-Hankel analysis',
 'relation':'These are two directional residual machines of the same exact coefficient series; neither count supersedes the other.'},'generator_cost':COST,'programs':{}}
for name,(path,D) in specs.items():
    d,w,n=load_program(path,D)
    rec={'degree':D,'support_count':len(n),'profiles':{}}
    for p in PRIMES:
        rec['profiles'][str(p)]={'algebra_build':profile(w,n,D,p,False),'column_execution':profile(w,n,D,p,True)}
    # promote first profile after checking all primes agree
    for mode in ('algebra_build','column_execution'):
        vals=[rec['profiles'][str(p)][mode] for p in PRIMES]
        if any(v!=vals[0] for v in vals[1:]): raise SystemExit(f'prime disagreement {name} {mode}')
        rec[mode]=vals[0]
    out['programs'][name]=rec
OUT.write_text(json.dumps(out,indent=2))
print(OUT)
for n,r in out['programs'].items():
    print(n,'alg',r['algebra_build']['primitive_calls'],r['algebra_build']['state_dims'],'phys',r['column_execution']['primitive_calls'],r['column_execution']['state_dims'])
