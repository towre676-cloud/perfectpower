"""Bounded deterministic discovery of the source seed; no CKM fit targets."""
from pathlib import Path
import json
import numpy as np
from develop_valentiner_frames import generators,group_closure,numeric
from valentiner_rank_lifting import *
ROOT=Path(__file__).resolve().parents[1]


def search():
    group=group_closure(generators())[0];rng=np.random.default_rng(672026);trials=[]
    for i,j,penalty in [(12,36,0),(12,36,30),(16,36,30),(36,12,30),(19,36,30),(12,19,30)]:
        v,b=numeric(group[i])[:,0],numeric(group[j])[:,0];x=pack(np.eye(3),np.diag([1.,0,0]).astype(complex),np.outer(v,b.conj()))
        for eps in [10,100,300]:
            z,r=solve(x+.003*rng.normal(size=54),eps,penalties=(penalty,penalty));L,A,B=unpack(z)
            yu=canonical_mediator(.9*np.eye(3),.1*A,h=.6)['Y'];yd=holomorphic_down_matching((.1*L).conj(),(.1*B).conj())['Y']
            ua,sa,_=np.linalg.svd(yu);ub,sb,_=np.linalg.svd(yd);V=ua[:,::-1].conj().T@ub[:,::-1];J=float(np.imag(V[0,0]*V[1,1]*V[0,1].conj()*V[1,0].conj()))
            trials.append({'indices':[i,j],'penalty':penalty,'epsilon':eps,'record':r,'spectra':[sa.tolist(),sb.tolist()],'J':J})
            if min(sa[-1],sb[-1])>1e-8 and abs(J)>1e-6 and r['minimum_real_Hessian_eigenvalue']>0:
                out={'indices':[i,j],'penalty':penalty,'epsilon':eps,'fields':z.tolist(),'record':r,'J':J}
                return out,trials
            x=z
    raise RuntimeError('No full-rank physical-CP witness in declared bounded search')


if __name__=='__main__':
    out,trials=search();p=ROOT/'receipts/m22_interactions'
    (p/'valentiner_rank_cp_positive.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    (p/'valentiner_rank_lifting_search.json').write_text(json.dumps({'trials':trials,'target_selection':'First stable full-rank weak-CP witness, not smallest CKM error or a nominated angle.'},indent=2,sort_keys=True)+'\n')
    print('retained',out['indices'],out['penalty'],out['epsilon'],out['J'],'trials',len(trials))
