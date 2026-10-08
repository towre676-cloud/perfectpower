"""Replay finite-mediator radiation nodes, detuning orders and fixed-Higgs inversion."""
from pathlib import Path
from dataclasses import replace
import json
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall,solve_coupled_wall
from perfectpower.wall_gaussian_fredholm import gaussian_node_response,fixed_Higgs_source_prediction,singlet_resolvent_check,exact_gaussian_portal_identities
from perfectpower.wall_embedded_states import localized_embedded_candidate
from perfectpower.wall_scattering import outgoing_shape_pole


def main():
    nodes=[]
    for a,mu in [(0.,10),(.1,10),(.8,3),(2.,3)]:
        response=gaussian_node_response(WallModel(1,.1,.025,mu,a))
        nodes.append({k:v for k,v in response.items() if k not in ['solutions','profile']})
    model=WallModel(1,.1,.025,3,2);r=gaussian_node_response(model)
    full={k:v for k,v in r.items() if k!='solutions'}
    controls=[]
    for R,tol in [(24,1e-9),(28,1e-10),(32,1e-11)]:
        z=gaussian_node_response(model,length=R,tol=tol)
        controls.append({k:z[k] for k in ['radius_x','tol','shape_energy_over_v2','leading_node_threshold_over_v2','linear_threshold_coefficient','maximum_residuals']})
    curves=[];widths=[]
    for kap in [5e-5,1e-4,2e-4,4e-4]:
        b=HiggsWall(portal=kap,lam=r['leading_node_threshold_over_v2']/2,v_GeV=1)
        c=localized_embedded_candidate(model,b,length=22,tol=1e-10)
        curves.append({'portal':kap,'full_tuned_threshold_over_v2':2*c['tuned_Higgs_lambda'],
            'difference_quotient_linear_coefficient':(2*c['tuned_Higgs_lambda']-r['leading_node_threshold_over_v2'])/kap,
            'predicted_linear_coefficient':r['linear_threshold_coefficient'],'boundary_residual':c['boundary_residual']})
        row={'portal':kap}
        for name,threshold in [('scalar_node',.1),('Gaussian_node',r['leading_node_threshold_over_v2']),
                ('Gaussian_corrected_node',r['leading_node_threshold_over_v2']+r['linear_threshold_coefficient']*kap)]:
            w=solve_coupled_wall(model,replace(b,lam=threshold/2),length_factor=22)
            row[name]=outgoing_shape_pole(w,tol=1e-10,energy_guess=r['shape_energy_over_v2'])
        widths.append(row)
    ratios={n:[widths[i+1][n]['width_GeV']/widths[i][n]['width_GeV'] for i in range(len(widths)-1)]
        for n in ['scalar_node','Gaussian_node','Gaussian_corrected_node']}
    physical_model=WallModel(30000,.1,.025,300000,3000);physical=[]
    for kap in [5e-8,1e-7,2e-7]:
        b=HiggsWall(portal=kap)
        pred=fixed_Higgs_source_prediction(physical_model,b)
        c=localized_embedded_candidate(physical_model,b,tune='source_lambda',length=22,tol=1e-10)
        physical.append({'prediction':pred,'independent_full_source_lambda':c['tuned_source_lambda'],
            'independent_full_mass_GeV':c['mass_GeV'],
            'source_lambda_prediction_error':pred['predicted_source_lambda']-c['tuned_source_lambda'],
            'scope':c['scope']})
    result={'scientific_base_head':'442f5e682a793b0235d59da25e33934bacb82119','exact_polynomial_identities':exact_gaussian_portal_identities(),
        'coupling_scan':nodes,'strong_Gaussian_response':full,'domain_controls':controls,
        'independent_heavy_resolvent_check':singlet_resolvent_check(r),'independent_nonlinear_curve':curves,
        'outgoing_width_cases':widths,'outgoing_width_doubling_ratios':ratios,
        'fixed_Higgs_physical_predictions':physical,'infinite_domain_existence_proved':False,'quantum_protection_derived':False,
        'scope':'Finite Gaussian gradients included at zero portal and in the first portal radiation correction. Derived coupled leading node, slope and fixed-Higgs source prediction; independent nonlinear and outgoing tests. No new coupled quadratic portal coefficient or physical stable-particle/cosmological claim.'}
    out=Path(__file__).resolve().parents[1]/'receipts/flavor_cosmology/wall_gaussian_fredholm.json'
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'node':r['leading_node_threshold_over_v2'],'slope':r['linear_threshold_coefficient'],'width_doubling_ratios':ratios,
        'physical_predictions':physical,'receipt':str(out)},indent=2))

if __name__=='__main__':main()
