"""Retuned wall-node continuation and independent outgoing-pole responses."""
from dataclasses import replace
from pathlib import Path
import json
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall,solve_coupled_wall
from perfectpower.wall_scattering import outgoing_shape_pole
from perfectpower.wall_embedded_states import leading_node_shift,independent_green_node_shift,localized_embedded_candidate
ROOT=Path(__file__).resolve().parents[1]


def outgoing(model,bath,energy=None):
    wall=solve_coupled_wall(model,bath,length_factor=18)
    return outgoing_shape_pole(wall,tol=1e-10,energy_guess=energy)


def main():
    coefficient=leading_node_shift();C=coefficient['threshold_shift_per_portal']
    m=WallModel(1,.1,.025,10,0);b=HiggsWall(portal=.001,lam=.05,v_GeV=1)
    corrected=[];sweep=[]
    for kap in [1e-4,2e-4,4e-4]:
        corrected.append({'portal':kap,'Higgs_lambda':(.1+C*kap)/2,
                          'outgoing_pole':outgoing(m,replace(b,portal=kap,lam=(.1+C*kap)/2))})
    for kap in [1e-5,1e-4,1e-3,.005]:
        r=localized_embedded_candidate(m,replace(b,portal=kap));sweep.append(r)
    controls=[localized_embedded_candidate(m,b,length=L,tol=t) for L,t in [(14,1e-8),(18,1e-9),(22,1e-10)]]
    tuned=controls[-1];detuning=[]
    for delta in [-.002,-.001,-.0005,0,.0005,.001,.002]:
        row={'relative_quartic_detuning':delta,'outgoing_pole':outgoing(m,replace(b,lam=tuned['tuned_Higgs_lambda']*(1+delta)),tuned['energy_over_v2'])}
        row['width_interpretation']='unresolved near-zero numerical output; not a lifetime or bound' if not delta else 'resolved radiative width'
        detuning.append(row)
    physical_model=WallModel(30000,.1,.025000033333333335,300000,3000);physical_bath=HiggsWall()
    physical=[localized_embedded_candidate(physical_model,physical_bath,tune='source_lambda',length=L,tol=1e-10) for L in [14,18,22]]
    pc=physical[-1];physical_poles=[]
    for delta in [-.001,0,.001]:
        model=replace(physical_model,lam=pc['tuned_source_lambda']*(1+delta))
        physical_poles.append({'relative_source_quartic_detuning':delta,'outgoing_pole':outgoing(model,physical_bath,pc['energy_over_v2']),
                               'width_interpretation':'unresolved near-zero numerical output; not a lifetime or bound' if not delta else 'resolved radiative width'})
    result={'baseline_commit':'06714d72ceadc7ec96ee97034cec5283bde298d8',
            'derived_node_shift':coefficient,'independent_Green_convolution':independent_green_node_shift(),
            'first_order_retuned_widths':corrected,'joint_Higgs_quartic_candidates':sweep,
            'radius_tolerance_candidate_controls':controls,'Higgs_quartic_detuning':detuning,
            'fixed_Higgs_parameters_source_quartic_candidates':physical,
            'fixed_Higgs_parameters_outgoing_detuning':physical_poles,
            'conclusions':{'first_order_node_correction_cancels_second_order_amplitude':True,
                           'sixth_power_width_supported_by_numerics':True,
                           'infinite_domain_BIC_existence_proved':False,'RG_protection_derived':False,
                           'previous_30_TeV_benchmark_source_quartic_unchanged':False},
            'execution_verified':False,'scope':'Perturbative overlap derivation and numerical finite-radius localized candidates with independent outgoing detuning. Source-quartic retuning is a new potential, so the previous benchmark thermal/network history does not carry over.'}
    target=ROOT/'receipts/flavor_cosmology/wall_embedded_states.json';target.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(target)

if __name__=='__main__':main()
