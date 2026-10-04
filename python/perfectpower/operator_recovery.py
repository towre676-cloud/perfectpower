"""Replay recovered operator calculus on actual staged recurrence candidates."""
from fractions import Fraction as Q
from collections import Counter
from .recurrence import Recurrence,scan_seq_directory
from .recurrence_identity import companion,compare_recurrences
from .exact_linear import (fitting_decomposition,target_factor,task_section,
                           intertwiner_space,context_profile,multiply,identity)
from .radical_arrows import ArrowElement
from .quotient_algebra import QuotientAlgebra,determinant
from . import polyalg as P


def _rec(record):return Recurrence(tuple(map(Q,record['coefficients'])),tuple(map(Q,record['initial'])))


def recovery_receipt(directory):
    atlas=scan_seq_directory(directory);models=[];gf=[]
    for entry in atlas['candidates']:
        model=_rec(entry);a=companion(model);fit=fitting_decomposition(a)
        models.append({'id':entry['id'],'offset':entry['offset'],'sha256':entry['sha256'],
                       'order':len(a),'stabilization_index':fit['stabilization_index'],
                       'nilpotent_dimension':fit['nilpotent_dimension'],'stable_dimension':fit['stable_dimension'],
                       'scope':'the reconstructed recurrence model, not the OEIS definition'})
        bridge=entry.get('supplied_GF_bridge')
        if bridge and bridge['prefix_matches']:
            source=_rec(bridge)
            shifted=Recurrence(source.coefficients,tuple(source.nth(entry['offset']+i) for i in range(len(source.coefficients))))
            gf.append({'id':entry['id'],'offset':entry['offset'],'sha256':entry['sha256'],
                       'comparison':compare_recurrences(model,shifted),'oeis_definition_proved':False})
    padovan=Recurrence((1,1,0),(1,1,1));fibonacci=Recurrence((1,1),(0,1))
    cubics=[]
    for name,modulus in [('Nahm free direction',(1,-1,-2,1)),('geometric critical factor',(-1,5,-4,1))]:
        algebra=QuotientAlgebra(modulus);theta=algebra.element((0,1));a=theta.matrix()
        disc=(-1)**3*P.resultant(P.poly(modulus),P.derivative(P.poly(modulus)))
        cubics.append({'name':name,'modulus':modulus,'polynomial_discriminant':disc,'theta_matrix':a,
                       'self_hom':intertwiner_space([a],[a])})
    arrow=ArrowElement((2,3,5),(1,-2,3,4,-5));reg=arrow.regular_matrix()
    return {'schema':'pp-operator-recovery/1','execution_verified':False,
            'source_scope':'recovered methods and two source cubics; no original Wilson carrier claimed',
            'staged_files':atlas['files'],'recurrence_models':len(models),
            'rejected_prefixes':len(atlas['rejections']),'fitting_models':models,
            'fitting_histogram':dict(Counter(f"nil={x['nilpotent_dimension']},stable={x['stable_dimension']}" for x in models)),
            'all_future_GF_model_comparisons':gf,
            'padovan_fitting':fitting_decomposition(companion(padovan)),
            'fibonacci_next_target':target_factor(((1,0),(0,1)),((1,1),)),
            'padovan_missing_third_coordinate':target_factor(((1,0,0),(0,1,0)),((0,0,1),)),
            'task_section':task_section(((1,0,0),(0,0,0)),((1,0,0,0),(0,0,0,0)),injective=True),
            'nonintegral_section':task_section(((1,),),((2,),)),
            'nilpotent_chain':fitting_decomposition(((0,1,0),(0,0,0),(0,0,2))),
            'source_cubics':cubics,
            'cubic_rank_profiles':[context_profile({f'power_{k}':_power(x['theta_matrix'],k) for k in range(1,6)}) for x in cubics],
            'cross_cubic_hom':intertwiner_space([cubics[0]['theta_matrix']],[cubics[1]['theta_matrix']]),
            'five_arrow_algebra':{'dimension':8,'radical_dimension':5,'radical_square_zero':True,
                 'regular_determinant':determinant(reg),'expected_regular_determinant':arrow.diagonal[0]**3*arrow.diagonal[1]**4*arrow.diagonal[2],
                 'carrier_determinant':determinant(arrow.carrier_matrix()),'expected_carrier_determinant':arrow.diagonal[0]*arrow.diagonal[1]*arrow.diagonal[2]**6,
                 'inverse_regular_identity':multiply(reg,arrow.inverse().regular_matrix())==identity(8)}}


def _power(a,k):
    out=identity(len(a))
    for _ in range(k):out=multiply(out,a)
    return out
