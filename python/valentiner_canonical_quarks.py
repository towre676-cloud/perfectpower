"""A distinct representation-enforced Nelson--Barr fermion assignment.

The scalar vacuum is unchanged. Q_L, u_R and d_R are neutral 3_u.
Each sector has singlet vectorlike triplets D=(3_d,0),
H_A=(3_H,-1,0), H_B=(3_H,0,-1). All ten allowed renormalizable
mass/Yukawa coefficients in each sector are nonzero real inputs.
The unique bare Higgs contraction is y I, and Higgs-to-heavy vertices
are forbidden at degree four by the product family representations.
"""
import numpy as np
from perfectpower.flavor_canonical import canonical_kernel

PARAMETERS = {
    'up':(.9,1.3,2.,.4,.2,.7,.3,1.,.23,.6),
    'down':(.8,1.7,2.3,.35,.21,.6,.2,.27,1.,.57),
}


def match(L,A,B,S,sector,mass_scale=1.):
    if sector not in PARAMETERS or not np.isfinite(mass_scale) or mass_scale<=0:
        raise ValueError('Specified sector and positive mass scale required')
    d,a,b,lf,lr,sf,sr,cl,ca,y=PARAMETERS[sector]
    I=np.eye(3);zero=np.zeros((3,3),complex)
    M=mass_scale*np.block([[d*I,zero,lf*B],
                          [zero,a*I,sf*S],
                          [lr*B.conj().T,sr*S.conj().T,b*I]])
    C=np.vstack([cl*L.conj().T,ca*A.conj().T,zero])
    F=np.hstack([C,M]);T=np.hstack([y*I,np.zeros((3,9))])
    # W M W^-1 is Hermitian: the interaction graph is a two-edge tree.
    weights=np.r_[np.full(3,np.sqrt(lr/lf)),np.full(3,np.sqrt(sr/sf)),np.ones(3)]
    similar=weights[:,None]*M/weights[None,:]
    kernel=canonical_kernel(F,T)
    kernel.update({'M':M,'C':C,'unnormalized_Y':y*I,'bare_y':y,
                   'hermitian_similarity':similar,'similarity_weights':weights,
                   'mass_scale':mass_scale})
    return kernel
