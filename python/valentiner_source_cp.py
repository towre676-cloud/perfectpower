"""Exact generalized-CP witnesses for all rank-one source-pair branches."""
from fractions import Fraction as Q
from math import lcm
import json
from pathlib import Path
import sympy as s
import numpy as np
from develop_valentiner_frames import generators,group_closure,numeric,product,conjugate,mul,IDENTITY,normalize,ONE,ZERO
ROOT=Path(__file__).resolve().parents[1]


def add(a,b):return tuple(x+y for x,y in zip(a,b))


def cp_matrix():
    rows=json.loads((ROOT/'receipts/m22_interactions/valentiner_cp.json').read_text())['unitary_CP_matrix'];out=[]
    for row in rows:
        for text in row:
            text=text.replace('sqrt(6 - 2*sqrt(5))','(sqrt(5)-1)').replace('sqrt(3 - sqrt(5))','((sqrt(5)-1)/sqrt(2))')
            z=s.sympify(text)
            re=s.expand(s.radsimp(s.simplify(s.re(z))));im=s.expand(s.radsimp(s.simplify(s.im(z)/s.sqrt(3))))
            b=re.coeff(s.sqrt(5));a=s.simplify(re-b*s.sqrt(5));d=im.coeff(s.sqrt(5));c=s.simplify(im-d*s.sqrt(5))
            a,b,c,d=map(Q,[a,b,c,d]);out.append((a+c,b+d,2*c,2*d))
    den=lcm(*(v.denominator for t in out for v in t))
    return normalize(den,tuple(tuple(int(v*den) for v in t) for t in out))


def conj_matrix(M):return M[0],tuple(conjugate(t) for t in M[1])


def vec(G):return [tuple(Q(v,G[0]) for v in G[1][3*i]) for i in range(3)]


def matvec(M,v):return [tuple(sum(product(tuple(Q(a,M[0]) for a in M[1][3*i+j]),v[j])[k] for j in range(3)) for k in range(4)) for i in range(3)]


def inner(v,w):return tuple(sum(product(conjugate(v[i]),w[i])[k] for i in range(3)) for k in range(4))


def power(a,n):
    out=ONE
    for _ in range(n):out=product(out,a)
    return out


def projector(v):return tuple(product(v[i],conjugate(v[j])) for i in range(3) for j in range(3))


def source_pair_cp_certificate():
    group=group_closure(generators())[0];X=cp_matrix();reps=[];keys=set()
    for k,G in enumerate(group):
        v=vec(G);key=projector(v)
        if key not in keys:keys.add(key);reps.append((k,v))
    assert len(reps)==45
    e=[ONE,ZERO,ZERO];candidate_matrices=[]
    for k,G in enumerate(group):
        U=mul(G,X);ue=vec(U)
        if ue[1:]!=[ZERO,ZERO]:continue
        candidate_matrices.append((k,U,ue[0]))
    choices=[]
    for ray,v in reps:
        row=[]
        for k,U,a in candidate_matrices:
            uv=matvec(U,[conjugate(t) for t in v]);b=inner(v,uv)
            if uv==[product(b,t) for t in v]:row.append((k,a,b))
        choices.append(row)
    witnesses=[];not_fixed=[]
    for (i,vi),ci in zip(reps,choices):
        for (j,vj),cj in zip(reps,choices):
            found=None
            for gi,a,b in ci:
                for gj,c,d in cj:
                    za=product(conjugate(a),c);zb=product(conjugate(b),d)
                    if power(za,6)==ONE and power(zb,6)==ONE:found=(gi,gj,za,zb);break
                if found:break
            if not found:
                not_fixed.append([i,j]);continue
            gi,gj,za,zb=found
            witnesses.append({'source_left_ray_element':i,'source_label_ray_element':j,'CP_left_group_element':gi,'CP_label_group_element':gj,
                              'C6_up_phase':[str(v) for v in za],'C6_down_phase':[str(v) for v in zb]})
    twist=ZERO
    for G in group:
        U=mul(X,conj_matrix(G));U2=mul(U,conj_matrix(U));tr=tuple(sum(Q(U2[1][3*i+i][k],U2[0]) for i in range(3)) for k in range(4))
        sy2=add(product(tr,tr),tuple(-v for v in tr));twist=add(twist,product(sy2,sy2))
    twist=tuple(v/Q(1080) for v in twist);assert twist==(Q(4),Q(0),Q(0),Q(0)),twist
    return {'axis_rays':45,'exact_CP_fixed_source_pairs':len(witnesses),'generalized_CP_square':'May be a residual family transformation; order two is not required for CP invariance.','source_shaping_group':'C6_A x C6_B',
            'exact_CP_trace_on_quartic_commutant':4,'complex_adjoint_quartics':6,'CP_even_adjoint_quartics':5,
            'source_pairs_without_a_CP_fixing_transformation':not_fixed,
            'ray_CP_group_candidates':[{'ray_element':i,'group_elements':[k for k,a,b in row]} for (i,v),row in zip(reps,choices)],
            'local_CP_persistence':'A CP-fixed isolated stationary point has a CP-fixed unique continuation under CP-even deformations until its Hessian becomes singular or the branch ends.',
            'witnesses':witnesses},group
