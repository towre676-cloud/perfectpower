"""Shared-adjoint Dirac messenger chains with representation-fixed vertices.

Heavy quarks have family spaces u,d,H. The H messenger has source charge
-B in the up sector and -A in the down sector. This permits S† and S,
respectively, to connect it to the bare right-handed H triplet.
"""
import numpy as np
from perfectpower.flavor_mediator import inverse_sqrt


def match(L,A,B,S,sector):
    if sector not in ['up','down']:raise ValueError('up or down sector required')
    eye=np.eye(3);zero=np.zeros((3,3),complex)
    mu=.9 if sector=='up' else .8
    source=B if sector=='up' else A
    M=np.block([[mu*eye,.71*L,zero if sector=='up' else .4*source],
                [.23*L.conj().T,1.3*eye,.4*source if sector=='up' else zero],
                [zero if sector=='up' else .2*source.conj().T,.2*source.conj().T if sector=='up' else zero,2*eye]])
    C=np.vstack([A if sector=='up' else zero,zero if sector=='up' else B,S.conj().T if sector=='up' else S])
    null=np.linalg.solve(M,C);K=np.eye(3)+null.conj().T@null;right=inverse_sqrt(K)
    frame=np.vstack([eye,-null])@right;heavy=np.hstack([C,M])
    h=.6 if sector=='up' else .57
    higgs_row=np.hstack([zero,h*eye,zero,zero])
    Y=-h*null[:3]@right
    assert np.max(abs(heavy@frame))<1e-11 and np.max(abs(frame.conj().T@frame-eye))<1e-11
    return {'Y':Y,'unnormalized_Y':-h*null[:3],'M':M,'C':C,'null_map':null,'light_right_frame':frame,'heavy_row':heavy,
            'higgs_row':higgs_row,'heavy_gap':float(min(np.linalg.svd(heavy,compute_uv=False)))}
