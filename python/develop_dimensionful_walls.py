"""Build a dimensionful wall-model benchmark and conditional cosmological scans."""
from dataclasses import asdict,replace
from pathlib import Path
from itertools import product
import json,hashlib
import numpy as np
from perfectpower.dimensionful_walls import *

ROOT=Path(__file__).resolve().parents[1]


def build():
    # These are declared choices, not fitted quark inputs or inferred scales.
    portal=1e-7
    base=WallModel(30000.,.1,.1/4+portal/3,300000.,3000.)
    wall=solve_wall(base)
    refined=solve_wall(base,length_factor=22.,tol=2e-10,nodes=1000)
    assert abs(wall['tension_GeV3']/refined['tension_GeV3']-1)<2e-9
    sigma=refined['tension_GeV3'];bounds=tension_bounds(base)
    assert bounds['lower_GeV3']<=sigma<=bounds['upper_GeV3']
    target_T=.03
    gap0=2*3*.8*sigma*radiation_H(target_T,10.75)
    model=WallModel(base.v_GeV,base.lam,base.thermal_c,base.heavy_mass_GeV,base.current_g_GeV,gap0/(2*base.v_GeV),3000.)
    bath=Higgs_bath_completion(model,portal=portal)
    low_T_model=replace(model,thermal_c=bath['low_temperature_source_thermal_c_after_Higgs_minimization'])
    ann=annihilation(low_T_model,sigma)
    vacua=thermal_vacua(low_T_model,ann['temperature_GeV'])
    gap_exact=float(vacua['exact_numeric_energy_gap_GeV4'])
    assert vacua['two_local_minima'] and abs(gap_exact/ann['bias_gap_GeV4']-1)<1e-12
    scenarios={
        'reference_scaling':gw_estimate(sigma,ann['H_GeV'],wall_inverse_width_GeV=model.v_GeV*sqrt(model.lam/2)),
        'delayed_emission_sensitivity':gw_estimate(sigma,ann['H_GeV'],emission_H_ratio=.1,peak_frequency_in_H=2.,middle_slope=-.5,uv_slope=-1.8,wall_inverse_width_GeV=model.v_GeV*sqrt(model.lam/2))}
    cutoff=.005;wall_budget=.1;gw_budget=1e-6
    # The true-vacuum additive constant is subtracted. A remaining false
    # volume costs DeltaV; late emission scenarios must also control it.
    false_fraction_at_ann=.5;false_fraction_at_emission=.01
    for g in scenarios.values():
        Hgw=g['emission_H_ratio']*ann['H_GeV']
        g['declared_remaining_false_volume_fraction']=false_fraction_at_emission
        g['false_vacuum_energy_fraction_screen']=false_fraction_at_emission*gap_exact/(3*MPL_REDUCED_GEV**2*Hgw*Hgw)
        g['total_defect_energy_fraction_screen']=g['false_vacuum_energy_fraction_screen']+g['hypothetical_scaling_wall_fraction_at_emission']
    barrier=model.lam*model.v_GeV**4/4
    screen={
        'unbiased_global_CP_pair':True,
        'post_inflation_restoration':10*model.critical_temperature_GeV>model.critical_temperature_GeV,
        'bias_turns_on_after_transition':model.bias_onset_GeV<model.critical_temperature_GeV,
        'tiny_bias_preserves_two_basins':gap_exact/barrier<.01 and vacua['two_local_minima'],
        'annihilation_before_declared_BBN_deadline':ann['temperature_GeV']>cutoff,
        'emission_before_declared_BBN_deadline':all(g['emission_temperature_GeV']>cutoff for g in scenarios.values()),
        'network_subdominant_at_annihilation':ann['wall_fraction']<wall_budget,
        'wall_plus_false_vacuum_subdominant_at_annihilation':ann['wall_fraction']+false_fraction_at_ann*gap_exact/(3*MPL_REDUCED_GEV**2*ann['H_GeV']**2)<wall_budget,
        'conservative_scaling_subdominant_through_emission':all(g['hypothetical_scaling_wall_fraction_at_emission']<wall_budget for g in scenarios.values()),
        'wall_plus_remaining_false_vacuum_subdominant_at_emission':all(g['total_defect_energy_fraction_screen']<wall_budget for g in scenarios.values()),
        'template_radiation_budget':all(g['integrated_Omega_h2']<gw_budget for g in scenarios.values()),
        'flat_UV_cap_radiation_budget':all(g['integrated_flat_UV_cap_Omega_h2']<gw_budget for g in scenarios.values()),
        'prompt_wall_scalar_decay':bath['leading_phi_to_hh_width_GeV']>100*ann['H_GeV']}
    assert all(screen.values())
    scan=[]
    # Deterministic coverage of stated nuisance choices, not a probability law.
    for A,C,eff,gstar,ratio in product([.6,.8,1.],[2.,3.,5.],[.3,.7,1.1],[10.75,17.25],[.1,.3,1.]):
        a=annihilation(low_T_model,sigma,area=A,annihilation_factor=C,gstar=gstar)
        g=gw_estimate(sigma,a['H_GeV'],area=A,efficiency=eff,gstar=gstar,gstar_s=gstar,emission_H_ratio=ratio,
                      peak_frequency_in_H=1. if ratio==1 else 2.,middle_slope=-1. if ratio==1 else -.5,uv_slope=-1. if ratio==1 else -1.8,
                      frequencies=[1e-9,1e-8,1e-7],wall_inverse_width_GeV=model.v_GeV*sqrt(model.lam/2))
        false_energy=false_fraction_at_emission*a['bias_gap_GeV4']/(3*MPL_REDUCED_GEV**2*(ratio*a['H_GeV'])**2)
        total_energy=g['hypothetical_scaling_wall_fraction_at_emission']+false_energy
        passed=(g['emission_temperature_GeV']>cutoff and total_energy<wall_budget and g['integrated_flat_UV_cap_Omega_h2']<gw_budget)
        scan.append({'area':A,'C_ann':C,'efficiency':eff,'gstar_equal_gstar_s':gstar,'emission_H_ratio':ratio,
                     'T_ann_GeV':a['temperature_GeV'],'T_emission_GeV':g['emission_temperature_GeV'],
                     'peak_frequency_Hz':g['peak_frequency_Hz'],'peak_Omega_h2':g['peak_Omega_h2'],
                     'wall_fraction_emission_screen':g['hypothetical_scaling_wall_fraction_at_emission'],
                     'total_defect_fraction_emission_screen':total_energy,
                     'integrated_flat_UV_cap_Omega_h2':g['integrated_flat_UV_cap_Omega_h2'],
                     'passes_declared_screen':passed})
    # Dimensional rescaling of the actual nonet action cannot turn a local
    # CP-breaking branch into global minima or change a dimensionless S4.
    original=json.loads((ROOT/'receipts/flavor_cosmology/tree_decay.json').read_text())
    joint=json.loads((ROOT/'receipts/m22_interactions/valentiner_nonet_joint.json').read_text())
    flavor_F=246./joint['canonical_coordinates'][-1]
    return {'schema':'pp-dimensionful-Gaussian-wall-cosmology/1',
            'baseline_commit':'4715d769d02bb381e98bc51435dfd4277bc2ae9c',
            'declared_model_inputs':asdict(model),'declared_bath_completion':bath,
            'input_vs_derived':'v, lambda, heavy mass/current, thermal bath, portal, radiation degrees, bias-onset history and network parameters are choices. The bias amplitude is chosen to place reference annihilation at 30 MeV; this temperature is a design target, not an independent prediction.',
            'potential':'V(phi,S,T)=lambda*(phi^2-v^2)^2/4+M^2*(S+g*phi^2/M^2)^2/2+c*T^2*phi^2/2-h(T)*phi, with h(T)=h0*max(0,1-(T/Tbias)^2). Higgs-bath square is separately specified.',
            'source_only_critical_temperature_GeV':model.critical_temperature_GeV,
            'unbiased_critical_temperature_GeV':bath['leading_three_field_CP_transition_GeV'],
            'transition_scope':'Second-order CP transition in the stated mean-field three-field thermal free energy, with Higgs thermal mass c_H*T^2 and h=0 near Tc. Positive Higgs curvature there selects H=0. Low-temperature gaps include Higgs thermal feedback by exact static minimization of its radial square. Full gauge/scalar resummation, higher thermal operators and defect formation are not computed.',
            'maximum_post_inflation_temperature_GeV':10*model.critical_temperature_GeV,
            'wall':refined,'wall_refinement_relative_difference':abs(wall['tension_GeV3']/sigma-1),
            'finite_temperature_vacua_at_annihilation':vacua,'annihilation':ann,'GW_scenarios':scenarios,
            'declared_screen_inputs':{'BBN_deadline_GeV':cutoff,'maximum_total_defect_fraction':wall_budget,'integrated_GW_budget_Omega_h2':gw_budget,
                'false_volume_fraction_at_annihilation_upper':false_fraction_at_ann,'false_volume_fraction_at_emission_upper':false_fraction_at_emission,
                'vacuum_constant':'Subtract the zero-temperature true vacuum energy; cosmological-constant matching is an input, not a prediction.'},
            'screen_results':screen,'passes_declared_wall_cosmology_screen':all(screen.values()),
            'nuisance_scan':scan,'nuisance_scan_summary':{'points':len(scan),'passes':sum(r['passes_declared_screen'] for r in scan),
                 'peak_frequency_Hz_range':[min(r['peak_frequency_Hz'] for r in scan),max(r['peak_frequency_Hz'] for r in scan)],
                 'peak_Omega_h2_range':[min(r['peak_Omega_h2'] for r in scan),max(r['peak_Omega_h2'] for r in scan)]},
            'published_nonet_flavor_branch':{'CP_breaking_global_vacua':False,'input_sha256':hashlib.sha256((ROOT/'receipts/flavor_cosmology/tree_decay.json').read_bytes()).hexdigest(),
                  'best_trial_S4':min(c['bubble']['dimensionless_action'] for c in original['candidates']),
                  'conditional_Higgs_normalization':{'declared_physical_Higgs_vev_GeV':246.,
                      'source_Higgs_coordinate':joint['canonical_coordinates'][-1],
                      'common_canonical_scale_GeV':flavor_F,'reference_mediator_mass_GeV':10*flavor_F,
                      'lower_competitor_energy_gap_GeV4':original['published_vacuum_status']['energy_gap']*flavor_F**4,
                      'normalization_assumption':'Identify the supplied canonical neutral Higgs coordinate with 246 GeV and V=F^4 Vhat. No physical mass fit or controlled quantum action follows from this identification.'},
                  'dimensional_scaling':'If canonical fields=F*z and V=F^4*Vhat(z), a static tension scales as F^3 and thermal temperatures scale as F. Zero-temperature S4 remains unchanged. A physical least-path bounce and normalization are still required.',
                  'scope':'No stable-wall/GW signal or cosmologically viable quark-flavor benchmark assigned to the non-global, quantum-uncontrolled retained branch.'},
            'primary_references':['https://arxiv.org/abs/1309.5001','https://arxiv.org/abs/2504.03636','https://arxiv.org/abs/2504.07902'],
            'remaining_physics':'This is a dimensionful spectator CP-wall benchmark passing declared network screens, not a cosmologically validated flavor model. Need full thermal action, defect/annihilation simulation, relic/entropy Boltzmann history and any coupling to matched quark observables. The supplied late CP bias is not a derived protection mechanism.',
            'formal_verification':False}


if __name__=='__main__':
    result=build();out=ROOT/'receipts/flavor_cosmology/dimensionful_walls.json';out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'sigma_GeV3':result['wall']['tension_GeV3'],'Tc_GeV':result['unbiased_critical_temperature_GeV'],
                      'Tann_GeV':result['annihilation']['temperature_GeV'],'GW':{k:[v['peak_frequency_Hz'],v['peak_Omega_h2']] for k,v in result['GW_scenarios'].items()},
                      'nuisance_scan':result['nuisance_scan_summary']}))
