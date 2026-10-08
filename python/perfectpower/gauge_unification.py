"""Conditional one-loop gauge predictions from two non-Abelian anchors.

UV gauge unification is an additional physical assumption, not implied by
finite flavor symmetry. No electromagnetic coupling is accepted as an input.
"""
from fractions import Fraction as Q

BASE = (Q(81,10), Q(-19,6), Q(-3))  # GUT-normalized U1, SU2, SU3 above all six heavy quarks


def predict(weak_inverse, strong_inverse, beta=BASE, *, offsets=(0,0,0)):
    """x_i=U+b_i*L+offset_i, L=log(Lambda/mu)/(2*pi).

    offsets encode explicitly supplied threshold corrections to inverse alpha.
    Returned electromagnetic coupling is at mu in this one-loop convention;
    it is not alpha(0) and includes no uncomputed low-energy matching.
    """
    if any(isinstance(x, float) for x in (weak_inverse,strong_inverse,*beta,*offsets)):
        raise ValueError('exact rational anchors, beta coefficients and offsets required')
    x2,x3=map(Q,(weak_inverse,strong_inverse));b1,b2,b3=map(Q,beta);o1,o2,o3=map(Q,offsets)
    if min(x2,x3)<=0:
        raise ValueError('positive inverse non-Abelian couplings required')
    if b2==b3:
        return {'status':'underdetermined' if x2-o2==x3-o3 else 'inconsistent',
                'electromagnetic_input_used':False}
    L=(x2-o2-x3+o3)/(b2-b3)
    U=x2-o2-b2*L
    x1=U+b1*L+o1
    assert x2==U+b2*L+o2 and x3==U+b3*L+o3
    return {'status':'physical_above_anchor' if min(L,U,x1)>0 else 'no_physical_UV_unification',
            'log_scale_over_2pi':str(L),'unified_inverse':str(U),
            'hypercharge_GUT_inverse':str(x1),
            'electromagnetic_inverse_at_anchor':str(x2+Q(5,3)*x1),
            'electromagnetic_input_used':False,'UV_unification_assumed':True,
            'low_energy_alpha0_predicted':False}


def triplet_atlas(weak_inverse, strong_inverse):
    """Frozen anomaly-safe Y=0 matter menu; no alpha-based candidate ranking.

    Majorana SU2 adjoint fermions shift b2 by 4/3; real adjoint scalars by 1/3.
    These representations are real, have no perturbative chiral anomalies,
    and have even SU2 global-anomaly index. This is a gauge-running extension,
    not a supplied scalar/Yukawa UV action or a phenomenology exclusion study.
    """
    rows=[]
    for fermions in range(7):
        for scalars in range(5):
            b=(BASE[0],BASE[1]+Q(4,3)*fermions+Q(1,3)*scalars,BASE[2])
            rows.append({'Majorana_Y0_triplets':fermions,'real_Y0_triplets':scalars,
                         'beta':list(map(str,b)),'prediction':predict(weak_inverse,strong_inverse,b)})
    return {'weak_inverse':str(Q(weak_inverse)),'strong_inverse':str(Q(strong_inverse)),
            'rows':rows,'menu_complete':True,'complete_over_all_matter':False,
            'electromagnetic_input_used':False,'common_threshold_assumed':True,
            'scope':'35 declared common-threshold one-loop gauge theories; no CKM or alpha(0) prediction'}
