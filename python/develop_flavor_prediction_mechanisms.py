"""Reproduce source-derived coupling rays, mixing moments and gauge designs."""
from pathlib import Path
from fractions import Fraction as Q
import json
from perfectpower.flavor_rg_rays import source_table, restrict, discover_rational_rays, su3_census, INDICES
from perfectpower.flavor_spectral_moments import moments, recover, jarlskog_squared, probability_chart, alignment_rank, su3_orientation
from perfectpower.gauge_unification import triplet_atlas

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions/flavor_prediction_mechanisms.json'


def tensor_replay(table):
    from valentiner_adjoint_quartics import quartic_projectors
    from perfectpower.exact_nonet_algebra import (certify_projectors,exact_quartics,
        verify_loop_table,padd,pscale,pmul,var,METRIC,ONE)
    P,_=quartic_projectors()
    A,D,certificate=certify_projectors(P)
    polys=exact_quartics(A,D)
    index={k:i for i,k in enumerate(INDICES)}
    retained=[[index[k],index[i],index[j],c] for k,i,j,c in table
              if k in index and i in index and j in index]
    proof=verify_loop_table([polys[k] for k in INDICES],retained)
    trace=padd(*(pscale(pmul(var(2+i),var(12+i)),(Q(g),Q(0))) for i,g in enumerate(METRIC)))
    expected=padd(pmul(trace,trace),pscale(polys[39],(-Q(1,8),Q(0))),
                  pscale(polys[48],(-Q(6,5),Q(0))))
    assert padd(polys[49],polys[50],polys[51])==expected
    return {'source_projectors':certificate,'restricted_exact_tensor_proof':proof,
            'SU3_trace_decomposition_coefficientwise':True}


def build():
    table,digest=source_table(ROOT);rows=restrict(table)
    census=su3_census(rows);search=discover_rational_rays(rows)
    orientations=[]
    for r in census['real_roots_including_zero']:
        if not r['zero_ray']:
            v=r['exact_coefficients']
            orientations.append({'coefficients':v,'orientation':su3_orientation(v),
                'stationary_chart_rank':alignment_rank([-5,-1,6],[-7,2,5],v)})
    p=probability_chart(Q(1,2),Q(1,3),Q(1,3),Q(1,3))
    M=moments([1,2,7],[3,5,11],p)
    assert recover([1,2,7],[3,5,11],M)==p
    result={'schema':'pp-flavor-prediction-mechanisms/1','CKM_inputs_used':False,
        'source_table_sha256':digest,'restricted_beta_tensor':[
            [[i,j,str(c)] for (i,j),c in sorted(row.items())] for row in rows],
        'source_tensor_replay':tensor_replay(table),'SU3_complete_census':census,
        'finite_channel_discovery':search,'orientation_results':orientations,
        'spectral_moment_example':{'up':[1,2,7],'down':[3,5,11],
            'probabilities':[[str(x) for x in row] for row in p],
            'moments':[[str(x) for x in row] for row in M],'J_squared':str(jarlskog_squared(p)),
            'input_kind':'synthetic exact model, not measured CKM'},
        'conditional_gauge_designs':triplet_atlas(30,9),
        'gauge_anchor_kind':'illustrative rational non-Abelian anchors, not a PDG fit',
        'physical_prediction_status':{'observed_CKM_derived':False,'alpha0_derived':False,
            'missing_CKM_mechanism':'isolated orientation from correlated noncentral interactions with enough independent invariant forces',
            'missing_alpha_mechanism':'justified UV normalization plus complete threshold and low-energy matching'},
        'sources':[{'title':'One-loop algebras and fixed flow trajectories in adjoint multi-scalar gauge theory',
                    'url':'https://arxiv.org/abs/2303.13884'},
                   {'title':'RG-stable parameter relations of a scalar field theory in absence of a symmetry',
                    'url':'https://arxiv.org/abs/2502.11011'}]}
    return result


if __name__=='__main__':
    result=build()
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'real_SU3_rays':result['SU3_complete_census']['nonzero_real_ray_count'],
        'exact_restricted_products':result['source_tensor_replay']['restricted_exact_tensor_proof']['symmetric_products_verified'],
        'gauge_models':len(result['conditional_gauge_designs']['rows']),
        'CKM_inputs_used':result['CKM_inputs_used']},indent=2))
