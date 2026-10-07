"""Regenerate wall poles, weak-portal/node scaling and real-axis scattering."""
from pathlib import Path
import json
from perfectpower.dimensionful_walls import WallModel,HBAR_GEV_S
from perfectpower.wall_fluctuations import HiggsWall,solve_coupled_wall
from perfectpower.wall_scattering import outgoing_shape_pole,wall_scattering,weak_portal_shape_width,exact_shape_channel_conditions
ROOT=Path(__file__).resolve().parents[1]


def main():
    m=WallModel(30000,.1,.025000033333333335,300000,3000)
    bath=HiggsWall();wall=solve_coupled_wall(m,bath)
    benchmark=[outgoing_shape_pole(wall,radius=wall['L']*f,tol=t) for f,t in [(1,1e-8),(.5,1e-9),(.75,1e-9),(1,1e-9)]]
    reference=benchmark[-1];reference['linear_mode_energy_lifetime_seconds']=HBAR_GEV_S/reference['width_GeV']
    weak=[]
    for kap in [1e-7,1e-6,1e-5]:
        model=WallModel(30000,.1,.025,300000,0);b=HiggsWall(portal=kap)
        w=solve_coupled_wall(model,b);p=outgoing_shape_pole(w,tol=1e-9)
        a=weak_portal_shape_width(model,b)
        weak.append({'portal':kap,'pole':p,'analytic':a,'numeric_to_leading_width':p['width_GeV']/a['width_GeV']})
    node=[]
    for kap in [1e-4,2e-4,4e-4,1e-3]:
        model=WallModel(1,.1,.025,10,0);b=HiggsWall(portal=kap,lam=.05,v_GeV=1)
        w=solve_coupled_wall(model,b)
        node.append({'portal':kap,'pole':outgoing_shape_pole(w,tol=1e-9),'exact_conditions':exact_shape_channel_conditions(model,b)})
    b=HiggsWall(portal=.01,v_GeV=3000);illustration=solve_coupled_wall(m,b)
    poles=[outgoing_shape_pole(illustration,radius=illustration['L']*f,tol=t) for f,t in [(.75,1e-9),(1,1e-8),(1,1e-9)]]
    e,im=poles[-1]['energy_over_v2'];curve=[]
    for d in [-8,-5,-3,-2,-1,-.5,-.25,0,.25,.5,1,2,3,5,8]:
        curve.append({'detuning_in_imaginary_energy_units':d,**wall_scattering(illustration,e+d*abs(im),tol=1e-8)})
    result={'benchmark_pole_controls':benchmark,'decoupled_weak_portal_sweep':weak,
            'polynomial_node_sweep':node,'illustrative_scattering_pole_controls':poles,
            'illustrative_scattering_parameters':{'portal':.01,'Higgs_v_GeV':3000.,'purpose':'wider resonance for resolved independent real-axis scattering; not the benchmark Higgs scale'},
            'real_axis_scattering':curve,
            'conclusions':{'benchmark_shape_is_decaying_resonance':True,'leading_form_factor_node_is_exact_BIC':False,
                           'continuum_stability_certified':False,'nonlinear_wall_network_simulated':False},
            'execution_verified':False,'scope':'Numerical outgoing BVP, independent real-axis flux calculations and exact leading form-factor polynomial. No new kernel proof, cosmological lifetime or physical CKM prediction.'}
    out=ROOT/'receipts/flavor_cosmology/wall_scattering.json';out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(out)

if __name__=='__main__':main()
