"""Replay distorted-wave widths and the physical TE thermal determinant."""
from pathlib import Path
import json
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall
from perfectpower.wall_gauge_channels import candidate_channel_solution
from perfectpower.wall_pair_decay import candidate_pair_data,continuum_pair_width
from perfectpower.wall_thermal_vectors import candidate_thermal_vectors


def compact(r):return {k:v for k,v in r.items() if not k.startswith('overlap_') and k!='normal_momentum_GeV'}


def main():
    m=WallModel(30000,.1,.025,300000,3000);b=HiggsWall()
    s=candidate_channel_solution(m,b)
    widths=[];fine_kernels={}
    for n,nx,order in [(97,1301,32),(193,2601,64),(289,3901,96)]:
        for channel in ['global_Goldstone','W_TE','Z_TE']:
            r=candidate_pair_data(s,channel=channel,g=.4,momentum_nodes=n,spatial_nodes=nx,order=order)
            widths.append(compact(r))
            if n==289:fine_kernels[channel]=r
            print(json.dumps(compact(r)),flush=True)
    scans=[]
    for g in [.3,.4,.5,.6,.65]:
        for channel in ['W_TE','Z_TE']:
            r=compact(candidate_pair_data(s,channel=channel,g=g,momentum_nodes=193,spatial_nodes=2601,order=64))
            scans.append({'declared_g':g,'declared_gprime':.36,**r})
    threshold_scan=[]
    critical_g=s['wall']['model'].v_GeV*s['mode_energy_over_v2']**.5/s['wall']['bath'].v_GeV
    for deficit in [.1,.03,.01,.003,.001,.0003,.0001,.00003]:
        g=(s['wall']['model'].v_GeV*s['mode_energy_over_v2']**.5-deficit)/s['wall']['bath'].v_GeV
        r=compact(candidate_pair_data(s,channel='W_TE',g=g,momentum_nodes=193,order=96))
        threshold_scan.append({'pair_energy_excess_GeV':deficit,'declared_g':g,**r})
    shorter=candidate_channel_solution(m,b,length=18)
    domains=[compact(candidate_pair_data(shorter,channel=c,g=.4)) for c in ['global_Goldstone','W_TE','Z_TE']]
    thermal_damping=[]
    for T in [25.,50.,100.,150.]:
        for channel,r in fine_kernels.items():
            rate=continuum_pair_width(r['mass_GeV'],r['bulk_mass_GeV'],r['normal_momentum_GeV'],
                [r['overlap_even_even_GeV_half'],r['overlap_odd_odd_GeV_half']],
                identical=channel!='W_TE',species=3 if channel=='global_Goldstone' else 1,order=96,temperature=T)
            thermal_damping.append({'channel':channel,'temperature_GeV':T,**rate,
                'ratio_to_zero_temperature_width':rate['width_GeV']/r['width_GeV']})
    thermal_damping_controls=[]
    r=fine_kernels['global_Goldstone']
    for order in [64,96,128]:
        rate=continuum_pair_width(r['mass_GeV'],0,r['normal_momentum_GeV'],
            [r['overlap_even_even_GeV_half'],r['overlap_odd_odd_GeV_half']],
            species=3,order=order,temperature=150)
        thermal_damping_controls.append({'phase_space_order':order,**rate})
    thermal=[]
    for n in [601,1201,2401,4801]:
        for T in [25.,50.,100.,150.]:
            thermal.append({'nodes':n,**candidate_thermal_vectors(s,T,nodes=n)})
    thermal_domain=[{'radius_x':R,**candidate_thermal_vectors(s,100,nodes=round(2400*R/22)+1,radius_x=R)} for R in [14.,18.]]
    extrapolated=[]
    for index,T in enumerate([25.,50.,100.,150.]):
        coarse=thermal[-8+index]['total_TE_thermal_free_energy_per_area_GeV3']
        fine=thermal[-4+index]['total_TE_thermal_free_energy_per_area_GeV3']
        extrapolated.append({'temperature_GeV':T,'O_spacing_squared_Richardson_GeV3':(4*fine-coarse)/3,
            'last_mesh_correction_GeV3':(coarse-fine)/3,'scope':'Numerical extrapolation, not an interval certificate.'})
    output={'scientific_base_head':'f40fd395e294576184a25e12de3df56da7d61f7f',
        'near_W_pair_threshold_scan':threshold_scan,'W_pair_critical_declared_g':critical_g,
        'thermal_spacing_extrapolation':extrapolated,'width_resolution_controls':widths,'gauge_coupling_scan':scans,'width_domain_18_controls':domains,
        'retarded_Bose_damping_quadrature_controls':thermal_damping_controls,
        'retarded_Bose_damping_on_fixed_wall':thermal_damping,'thermal_resolution_controls':thermal,'thermal_domain_controls':thermal_domain,
        'normal_momentum_conserved':False,'parallel_momentum_conserved':True,
        'Goldstone_and_vector_widths_same_theory':False,
        'complete_WW_ZZ_polarization_sum_computed':False,'full_nonlinear_lifetime_simulated':False,
        'renormalized_zero_temperature_determinant_computed':False,'nucleation_recomputed':False,
        'scope':'Distorted-wave leading cubic widths in the ungauged global Goldstone theory, and a separately gauged physical TE vector partial width; UV-finite one-loop TE thermal relative determinant on the fixed wall. Finite-domain numerical controls, no interval certificate. Other vector polarizations, off-shell, fermion and loop channels, thermal wall relaxation, Debye/daisy and two-loop terms remain open.'}
    p=Path(__file__).resolve().parents[1]/'receipts/flavor_cosmology/wall_pair_decay.json'
    p.write_text(json.dumps(output,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'thermal_final':thermal[-1],'receipt':str(p)},indent=2),flush=True)

if __name__=='__main__':main()
