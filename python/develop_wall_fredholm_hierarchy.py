"""Replay the second radiation cancellation and independent coupled controls."""
from dataclasses import replace
from pathlib import Path
import json
import numpy as np
from perfectpower.wall_fredholm_hierarchy import universal_responses,retuning_coefficients,threshold_series,exact_hierarchy_identities
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall,solve_coupled_wall
from perfectpower.wall_embedded_states import localized_embedded_candidate
from perfectpower.wall_scattering import outgoing_shape_pole


def main():
    r=universal_responses()
    simple={k:v for k,v in r.items() if k!='solutions'}
    x=np.linspace(0,20,401)
    simple['profile']={'x':x.tolist(),**{n:s.sol(x)[0].tolist() for n,s in r['solutions'].items()}}
    domain=[]
    for R in [24,28,32]:
        v=universal_responses(radius_x=R)
        domain.append({k:v[k] for k in ['radius_x','tol','linear_threshold_coefficient','quadratic_Higgs_coefficient','quadratic_source_coefficient','shape_energy_coefficient','maximum_response_residuals']})
    curves=[]
    for lam,h0 in [(.1,1),(.2,.5),(.07,1.5)]:
        model=WallModel(1,lam,.025,10,0);coef=retuning_coefficients(lam,h0,responses=r)
        cases=[]
        for kap in [5e-5,1e-4,2e-4,4e-4]:
            candidate=localized_embedded_candidate(model,HiggsWall(portal=kap,lam=lam/(2*h0*h0),v_GeV=h0),length=22,tol=1e-10)
            cases.append({'portal':kap,'coupled_threshold':2*candidate['tuned_Higgs_lambda']*h0*h0,
                'coupled_energy':candidate['energy_over_v2'],
                'quadratic_threshold_difference_quotient':(candidate['threshold_shift_from_scalar_node']-coef['linear_threshold_coefficient']*kap)/kap**2,
                'quadratic_energy_difference_quotient':(candidate['energy_over_v2']-1.5*lam)/kap**2,
                'boundary_residual':candidate['boundary_residual'],
                'maximum_BVP_relative_residual':candidate['maximum_BVP_relative_residual']})
        curves.append({'predicted_coefficients':coef,'independent_nonlinear_cases':cases})
    widths=[];model=WallModel(1,.1,.025,10,0)
    for kap in [.000125,.00025,.0005,.001]:
        pred=threshold_series(kap,.1,1,responses=r)
        row={'portal':kap,'predicted_series':pred}
        for order in [1,2]:
            threshold=.1+r['linear_threshold_coefficient']*kap if order==1 else pred['threshold_through_quadratic']
            bath=HiggsWall(portal=kap,lam=threshold/2,v_GeV=1)
            wall=solve_coupled_wall(model,bath,length_factor=22)
            row['order_'+str(order)+'_outgoing']=outgoing_shape_pole(wall,tol=1e-11,energy_guess=pred['shape_energy_through_quadratic'])
        widths.append(row)
    ratios=[widths[i+1]['order_2_outgoing']['width_GeV']/widths[i]['order_2_outgoing']['width_GeV'] for i in range(len(widths)-1)]
    result={'scientific_base_head':'8bc3af55098d9a0f489df757facb151f155f9867',
            'exact_polynomial_identities':exact_hierarchy_identities(),'universal_responses':simple,
            'response_domain_controls':domain,'independent_parameter_families':curves,
            'first_vs_second_correction_outgoing_widths':widths,'quadratic_correction_doubling_ratios':ratios,
            'infinite_domain_existence_proved':False,'quantum_protection_derived':False,
            'scope':'New derived quadratic retuning and quadratic shape energy for g=0. Exact symbolic force extraction, numerical Fredholm coefficients and independent nonlinear/outgoing controls. No fitted quartic or width coefficients, certified remainder, Gaussian-coupled extension or complete flavor vacuum.'}
    out=Path(__file__).resolve().parents[1]/'receipts/flavor_cosmology/wall_fredholm_hierarchy.json'
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'universal_coefficients':{k:simple[k] for k in ['linear_threshold_coefficient','quadratic_Higgs_coefficient','quadratic_source_coefficient','shape_energy_coefficient']},'width_doubling_ratios':ratios,'receipt':str(out)},indent=2))

if __name__=='__main__':main()
