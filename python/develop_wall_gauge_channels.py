"""Replay exact channel operators, Ward overlaps and vector threshold screens."""
from pathlib import Path
import json
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall
from perfectpower.wall_gauge_channels import exact_channel_identities,candidate_channel_solution,analyze_channels


def main():
    m=WallModel(30000,.1,.025,300000,3000);b=HiggsWall()
    controls=[];full=None;solution=None
    for length,tol in [(14,1e-9),(18,1e-10),(22,1e-10)]:
        s=candidate_channel_solution(m,b,length=length,tol=tol);report=analyze_channels(s)
        controls.append({'length':length,'tol':tol,**{k:v for k,v in report.items() if k!='profile'}})
        if length==22:full=report;solution=s
    scans=[]
    for g in [.4,.6,.65,.8]:
        r=analyze_channels(solution,g=g)
        scans.append({k:r[k] for k in ['declared_g','declared_gprime','mass_GeV','two_W_threshold_GeV','two_Z_threshold_GeV',
            'bulk_WW_pair_open','bulk_ZZ_pair_open','W_mass_vertex_integrated_form_factor_GeV_half','Z_mass_vertex_integrated_form_factor_GeV_half']})
    out={'scientific_base_head':'eb1fb27c7b546dbef211ddf0ee07c6dac4ffd672','exact_channel_identities':exact_channel_identities(),
        'physical_scale_candidate':full,'domain_controls':controls,'declared_gauge_input_scan':scans,
        'linear_radial_to_gauge_Goldstone_mixing':False,'Goldstone_longitudinal_derivative_mixing_retained':True,
        'global_Goldstones_are_physical_after_gauging':False,'complete_decay_width_computed':False,
        'continuum_profile_hypotheses_interval_certified':False,
        'scope':'Exact quadratic separation, global angular factorization and physical Proca factorization, conditional vacuum-threshold bounds, nonzero cubic Ward overlaps and benchmark pair thresholds. Finite profiles support hypotheses numerically; off-shell, loop and fermion widths remain uncomputed.',
        'primary_reference':'Takahiro Kubota, Gauge fields in the presence of the electroweak bubble wall, JHEP03(2026)089, https://arxiv.org/abs/2507.20134'}
    path=Path(__file__).resolve().parents[1]/'receipts/flavor_cosmology/wall_gauge_channels.json'
    path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:full[k] for k in ['mass_GeV','two_W_threshold_GeV','two_Z_threshold_GeV','global_Goldstone_Ward_relative_error','global_Goldstone_zero_energy_pair_overlap_GeV_half']},indent=2))

if __name__=='__main__':main()
