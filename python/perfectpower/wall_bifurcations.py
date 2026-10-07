"""Exact fold/cusp tests for the supplied Gaussian + Higgs mean-field action.

The polynomial variable s is T^2/v^2. No network or tunnelling rate follows
from a stationary-point discriminant. Fractions encode the supplied inputs.
"""
from fractions import Fraction as Q
from . import polyalg as P
from .core import evaluate
from .wall_vacuum_branches import _parameters, real_root_intervals, sign_at_root


def branch_polynomials(model, bath, *, thermal_higgs_c=.4):
    z = _parameters(model, bath, 0, thermal_higgs_c)
    l, k, H, d, c, ch, v = [z[n] for n in ('lam','k','lH','d','c','cH','v')]
    b0 = z['b']
    onset = Q(str(model.bias_onset_GeV))
    b = P.poly((b0, -b0*v*v/onset**2)) if b0 else P.poly((0,))
    result = {}
    for name, L, a in (
        ('Higgs_boundary', l+k*k/H, P.poly((l+k*d+k*k/H, -c))),
        ('Higgs_broken', l, P.poly((l, -(c-k*ch/H))))):
        # For F=L*u^3-a*u-b, discr(F)=L*(4*a^3-27*L*b^2).
        D = P.subtract(P.scale(P.mul(P.mul(a,a),a),4), P.scale(P.mul(b,b),27*L))
        # At a fold u^2=a/(3L). This face test is polynomial in s.
        wfold = P.subtract(P.poly((d+k/H, -ch/H)), P.scale(a,k/(3*H*L)))
        result[name] = {'L': L, 'a': a, 'b': b, 'D': D, 'w_at_fold': wfold}
    return result


def stationary_cubic_type(L, a, b):
    """Exact root multiplicities and source-curvature types, before face tests."""
    L, a, b = map(lambda x: Q(str(x)), (L,a,b))
    if L <= 0:
        raise ValueError('positive quartic coefficient required')
    D = 4*a**3-27*L*b*b
    if a == b == 0:
        label, distinct, multiplicities = 'cusp', 1, [3]
    elif D == 0:
        label, distinct, multiplicities = 'fold', 2, [2,1]
    elif D > 0:
        label, distinct, multiplicities = 'two_source_minima_and_barrier', 3, [1,1,1]
    else:
        label, distinct, multiplicities = 'one_source_minimum', 1, [1]
    answer = {'reduced_discriminant': str(D), 'type': label,
              'distinct_real_roots': distinct, 'multiplicities': multiplicities}
    if label == 'fold':
        answer.update(double_source_root=str(-3*b/(2*a)), simple_source_root=str(3*b/a),
                      double_source_curvature='0', simple_source_curvature=str(3*a))
    return answer


def late_bias_fold_census(model, bath, *, thermal_higgs_c=.4, bits=120):
    """All folds strictly inside the bias-on window, plus both endpoint events.

    Roots outside [0,(T_on/v)^2] are excluded by exact sign-at-root tests.
    Physical Higgs faces are tested separately, so a cubic fold on an unstable
    boundary is never reported as a loss of a metastable physical vacuum.
    """
    if not model.bias_h0_GeV3:
        raise ValueError('a positive late bias is required')
    z = _parameters(model,bath,0,thermal_higgs_c)
    stop = (Q(str(model.bias_onset_GeV))/z['v'])**2
    branches = branch_polynomials(model,bath,thermal_higgs_c=thermal_higgs_c)
    result = {'variable':'s=T^2/v^2', 'active_window_s':['0',str(stop)],
              'branches':{}, 'physical_fold_events':[], 'endpoint_events':[]}
    for name, q in branches.items():
        D, a, b = q['D'], q['a'], q['b']
        events=[]
        for root in real_root_intervals(D,bits=bits):
            left = sign_at_root(D,P.X,root)
            right = sign_at_root(D,P.poly((-stop,1)),root)
            if left < 0 or right > 0:
                continue
            positive_a = sign_at_root(D,a,root)>0
            positive_b = sign_at_root(D,b,root)>0
            face = sign_at_root(D,q['w_at_fold'],root)
            physical = positive_a and positive_b and (face>0 if name=='Higgs_broken' else face<0)
            endpoint = left==0 or right==0
            event={'s_interval':list(map(str,root)), 'positive_a':positive_a,
                   'positive_bias':positive_b, 'Higgs_squared_sign_at_fold':face,
                   'physical_metastable_fold':physical, 'Higgs_face_junction':face==0,
                   'endpoint':endpoint,
                   'double_source_root_formula':'u=-3*b(s)/(2*a(s)); u^2=a(s)/(3*L)'}
            events.append(event)
            if physical:
                result['physical_fold_events'].append({'Higgs_branch':name,**event})
            if endpoint:
                result['endpoint_events'].append({'Higgs_branch':name,**event})
        result['branches'][name]={'quartic_L':str(q['L']),
            'a_coefficients':list(map(str,a)), 'active_bias_coefficients':list(map(str,b)),
            'reduced_discriminant_coefficients':list(map(str,D)),
            'Higgs_squared_at_fold_coefficients':list(map(str,q['w_at_fold'])),
            'discriminant_sign_at_zero':(evaluate(D,0)>0)-(evaluate(D,0)<0),
            'discriminant_sign_at_onset':(evaluate(D,stop)>0)-(evaluate(D,stop)<0),
            'all_active_window_events':events}
    result['scope']='Complete exact polynomial fold census for this supplied mean-field spectator action during its late-bias window. Higgs face junctions are marked separately. This is not a tunnelling, network-annihilation, gauge-resummed thermal or nonet flavor result.'
    return result
