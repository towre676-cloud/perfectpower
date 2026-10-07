"""Produce the three-field wall, fluctuation and exact thermal branch advance."""
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
from math import sqrt
import hashlib,json
import numpy as np
from scipy.integrate import quad
from perfectpower.dimensionful_walls import WallModel,Higgs_bath_completion
from perfectpower.wall_fluctuations import HiggsWall,solve_coupled_wall,fluctuation_spectrum,scalar_reference
from perfectpower.wall_vacuum_branches import unbiased_global_vacuum,biased_stationary_branches,exact_transition_temperatures_squared,real_root_intervals,sign_at_root
from perfectpower import polyalg as P

ROOT=Path(__file__).resolve().parents[1]


def main():
    source=ROOT/'receipts/flavor_cosmology/dimensionful_walls.json'
    old=json.loads(source.read_text());inputs=old['declared_model_inputs']
    model=replace(WallModel(**inputs),bias_h0_GeV3=0.,bias_onset_GeV=0.)
    bath_inputs=old['declared_bath_completion']
    bath=HiggsWall(bath_inputs['portal_kappa'],bath_inputs['Higgs_lambda'],bath_inputs['Higgs_v_GeV'])
    cH=bath_inputs['declared_Higgs_thermal_c'];wall=solve_coupled_wall(model,bath)
    levels=[fluctuation_spectrum(wall,central_nodes=n) for n in (250,500,1000)]
    box=[]
    for length in (8.,16.):
        w=solve_coupled_wall(model,bath,length_factor=length)
        box.append({'length_factor':length,'wall':{k:v for k,v in w['report'].items() if k!='profile'},'spectrum':fluctuation_spectrum(w,central_nodes=500)})
    biased=WallModel(**inputs)
    snapshots=[biased_stationary_branches(biased,bath,Q(str(t)),thermal_higgs_c=cH) for t in (0.,.03,100.,140.,141.,200.,2999.,3000.,60000.,70000.)]
    trans=exact_transition_temperatures_squared(model,bath,thermal_higgs_c=cH)
    trans['CP_transition_GeV']=sqrt(float(Q(trans['CP_transition_GeV2'])))
    trans['Higgs_transition_GeV']=sqrt(float(Q(trans['Higgs_transition_GeV2'])))
    k=sqrt(model.lam/2);h0=bath.v_GeV/model.v_GeV;mh=sqrt(2*bath.lam)*h0
    integral=quad(lambda r:np.exp(-mh*r)/np.cosh(k*r)**2,0,100/k,epsabs=1e-12)[0]
    linear_shift=model.v_GeV*bath.portal*h0/mh*integral
    spinodal=P.poly((2,-3,0,1));roots=real_root_intervals(spinodal,bits=100)
    domain={'polynomial':list(map(str,spinodal)),'distinct_real_roots':list(map(lambda r:list(map(str,r)),roots)),
            'signs_of_denominator_u_minus_1':[sign_at_root(spinodal,(-1,1),r) for r in roots],
            'signs_of_curvature':[sign_at_root(spinodal,P.derivative(spinodal),r) for r in roots],
            'meaning':'The u=1 double-root/spinodal branch and the vanishing-denominator branch are retained, not divided away.'}
    r={'input_dimensionful_receipt_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
       'declared_model':model.__dict__,'declared_Higgs':bath.__dict__,'thermal_Higgs_c':cH,
       'scalar_reference':scalar_reference(model),'three_field_wall':wall['report'],
       'analytic_tension_bounds':Higgs_bath_completion(model)['three_field_tension_bounds_GeV3'],
       'linear_Higgs_center_shift_GeV':linear_shift,
       'mesh_refinements':levels,'box_refinements':box,'exact_transitions':trans,
       'zero_temperature_global_vacua':unbiased_global_vacuum(model,bath,0,thermal_higgs_c=cH),
       'thermal_stationary_snapshots':snapshots,'exceptional_branch_fixture':domain,
       'conclusions':{'all_finite_matrices_positive':all(s[p]['finite_matrix_Cholesky_positive'] for s in levels+[x['spectrum'] for x in box] for p in ('translation','opposite')),
                      'finest_translation_eigenvalue_over_v2':levels[-1]['translation']['eigenvalues_over_v2'][0],
                      'finest_translation_overlap':levels[-1]['translation']['translation_overlaps'][0],
                      'source_shape_is_above_Higgs_continuum':True,
                      'certified_coupled_continuum_stability':False,
                      'resonance_width_computed':False,
                      'network_GW_prediction_changed':False,
                      'physical_flavor_vacuum_classified':False},
       'source_inspiration':{'openai_math_tree':'adc7f1241b42e322a6451854ab7e4b4c146bf78a',
                            'family_142':'finite polynomial quotient, gcd detection of exceptional zero branches; repository rational/Sturm primitives reused',
                            'family_141':'real algebraic branch labels and constrained minimum formulation; here reduced to a strictly convex exact amplitude problem',
                            'families_262_375':'one-dimensional spectral analysis and scalar quartic interface normalization; no new headline conjecture is assumed'},
       'scope':'New results concern only the supplied spectator Gaussian + radial Higgs mean-field action. Exact homogeneous global selection, numerical coupled wall and finite-box spectra. No nonet flavor global minimum, continuum spectrum certificate, angular/gauge fluctuation calculation, or network simulation.'}
    target=ROOT/'receipts/flavor_cosmology/wall_stability.json';target.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'CP_transition_GeV':trans['CP_transition_GeV'],'Higgs_transition_GeV':trans['Higgs_transition_GeV'],
                      'central_Higgs_GeV':wall['report']['central_Higgs_GeV'],
                      'linear_Higgs_shift_GeV':linear_shift,
                      'translation_refinement':[s['translation']['eigenvalues_over_v2'][0] for s in levels],
                      'finite_matrix_positivity':r['conclusions']['all_finite_matrices_positive']},indent=2))


if __name__=='__main__':main()
