"""Recovered task sections applied to the repo's actual field-756 packets.

The signed unit box is finite. Imported exponent bounds remain imported.
"""
from fractions import Fraction as Q
from itertools import product
from .quotient_algebra import QuotientAlgebra
from .exact_linear import multiply,identity,intertwiner_space,injective_coordinates,solve


def _vector(element):return tuple(element.coefficients)+(Q(0),)*(element.algebra.degree-len(element.coefficients))


def field_operator_replay(packet,*,radius=3):
    if type(radius) is not int or radius<0 or radius>20:raise ValueError('box radius must be an integer from zero to twenty')
    p,q=packet['P'],packet['Q']
    arrays=list(packet['units'])
    for cl in packet['classes']:
        if type(cl['M']) is not int:raise ValueError('integer norm target required')
        arrays += [cl['form'],cl['phi']]+list(cl['gammas'])+list(cl['pari_thue'])
    if type(p) is not int or type(q) is not int or any(type(x) is not int for row in arrays for x in row):
        raise ValueError('source packet entries must be exact integers')
    algebra=QuotientAlgebra((-q,-p,0,1))
    units=tuple(algebra.element(u) for u in packet['units'])
    if len(units)!=2 or any(abs(u.norm())!=1 for u in units):raise ValueError('two norm-one or norm-minus-one units required')
    matrices=tuple(u.matrix() for u in units)
    if multiply(*matrices)!=multiply(*reversed(matrices)):raise AssertionError('noncommuting unit operators')
    if any(any(x.denominator!=1 for row in u.inverse().matrix() for x in row) for u in units):
        raise ValueError('unit inverse does not preserve the supplied coefficient order')
    exponents=tuple(range(-radius,radius+1));powers=[{r:u**r for r in exponents} for u in units]
    classes=[]
    for cl in packet['classes']:
        form=tuple(cl['form']);phi=algebra.element(cl['phi']);leading=form[0]
        carrier=tuple((leading if i==0 else 0,-_vector(phi)[i]) for i in range(3))
        # Norm(c0*a-phi*b) is homogeneous cubic; four b=1 evaluations determine it.
        values=[(algebra.element((leading*a,))-phi).norm() for a in range(4)]
        coefficients=solve(tuple(tuple(Q(a)**j for j in range(4)) for a in range(4)),values)
        if coefficients!=tuple(Q(leading**2*c) for c in reversed(form)):
            raise ValueError('source binary cubic does not match its norm carrier')
        expected=leading**2*cl['M'];accepted={};nonintegral=0;outside=0;wrong_norm=0;trials=0
        for seed in cl['gammas']:
            gamma=algebra.element(seed)
            if gamma.norm()!=expected:raise ValueError('seed has wrong prescribed norm')
            for r,s,sign in product(exponents,exponents,(-1,1)):
                trials+=1;alpha=gamma*powers[0][r]*powers[1][s]*sign
                if alpha.norm()!=expected:wrong_norm+=1;continue
                result=injective_coordinates(carrier,_vector(alpha))
                if result['status']=='IMAGE_OBSTRUCTION':outside+=1;continue
                if not result['integral_column_lattice_member']:nonintegral+=1;continue
                a,b=map(int,result['coordinates']);value=sum(c*a**(3-i)*b**i for i,c in enumerate(form))
                if value!=cl['M']:raise AssertionError('decoded point violates binary cubic')
                accepted.setdefault((a,b),[]).append({'seed':seed,'exponents':[r,s],'sign':sign})
        imported=[]
        for a,b in cl['pari_thue']:
            alpha=algebra.element((leading*a,))-phi*b;coords=injective_coordinates(carrier,_vector(alpha))
            if coords['coordinates']!=(a,b) or alpha.norm()!=expected:
                raise ValueError('imported point fails exact carrier replay')
            imported.append({'point':[a,b],'replayed':True,'found_in_box':(a,b) in accepted})
        classes.append({'class':cl['class'],'form':form,'M':cl['M'],'carrier':carrier,
                        'norm_form_coefficients_low_to_high':coefficients,'norm_form_identity':True,
                        'trials':trials,'wrong_norm':wrong_norm,'outside_rational_plane':outside,
                        'nonintegral_coordinates':nonintegral,
                        'points':[{'point':point,'witnesses':witnesses} for point,witnesses in sorted(accepted.items())],
                        'imported_points_replayed':imported,'complete_thue_solution_set_claimed':False})
    return {'schema':'pp-norm-operator-replay/1','field_modulus':(-q,-p,0,1),'radius':radius,
            'unit_matrices':matrices,'unit_norms':[u.norm() for u in units],
            'unit_inverse_preserves_coefficient_order':True,'units_commute':True,
            'simultaneous_unit_centralizer':intertwiner_space(matrices,matrices),
            'classes':classes,'scope':'signed unit exponents in the supplied finite box, plus replay of listed source points',
            'external_height_bound_reproved':False,'execution_verified':False}
