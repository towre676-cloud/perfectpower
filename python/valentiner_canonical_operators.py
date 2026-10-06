"""Enumerate renormalizable fermion contractions for the NB assignment.

Triplet intertwiner multiplicities and the adjoint insertion are certified by
exact 3.A6 characters. Phase charges are residues modulo six. Gauge quantum
numbers permit heavy Dirac masses and Q-Higgs-right Yukawas only.
"""
from fractions import Fraction as Q
from develop_valentiner_frames import generators,group_closure,product,conjugate
from develop_valentiner_invariants import Z,O,add,sub,scale,exact_integer

FERMIONS={'bare':('u',(0,0)),'D':('d',(0,0)),'H_A':('H',(-1,0)),'H_B':('H',(0,-1))}
SCALARS=[('L','u','d',(0,0)),('A','u','H',(1,0)),('B','d','H',(0,1)),('S','H','H',(-1,1))]


def certificate():
    group=group_closure(generators())[0];sums=[Z,Z,Z]
    for g in group:
        tr=tuple(sum(Q(g[1][3*i+i][j],g[0]) for i in range(3)) for j in range(4))
        norm=product(tr,conjugate(tr));adj=sub(norm,O)
        sums[0]=add(sums[0],norm);sums[1]=add(sums[1],adj);sums[2]=add(sums[2],product(adj,norm))
    dims=[exact_integer(scale(x,Q(1,len(group)))) for x in sums];assert dims==[1,0,1]
    scalars=SCALARS+[(name+'-dagger',b,a,tuple(-q for q in charge)) for name,a,b,charge in SCALARS]
    terms=[]
    for left,(family,charge) in FERMIONS.items():
        if left=='bare':continue
        for right,(rf,rq) in FERMIONS.items():
            required=tuple((a-b)%6 for a,b in zip(charge,rq))
            if family==rf and required==(0,0):terms.append({'left':left,'right':right,'scalar':'identity','multiplicity':1})
            for name,to,fr,cq in scalars:
                if family==to and rf==fr and tuple(q%6 for q in cq)==required:
                    terms.append({'left':left,'right':right,'scalar':name,'multiplicity':1})
    higgs=[right for right,(family,charge) in FERMIONS.items() if family=='u' and all(q%6==0 for q in charge)]
    assert len(terms)==9 and higgs==['bare']
    return {'group_order':len(group),'exact_character_multiplicities':{'triplet_endomorphism':dims[0],'adjoint_singlet':dims[1],'triplet_adjoint_triplet':dims[2]},
            'mass_and_source_contractions':terms,'Higgs_right_fields':higgs,'independent_real_renormalizable_coefficients':10,
            'scope':'One charge sector, color-triplet electroweak singlets. Canonical derivative terms. No higher-degree Yukawa or scalar/matter operators included.'}
