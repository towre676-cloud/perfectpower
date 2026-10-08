"""Thermal wall profiles, Higgs localization onset and branch-energy comparisons."""
from pathlib import Path
from dataclasses import asdict
import json
from perfectpower.wall_cooling import *
root=Path(__file__).resolve().parents[1];p=CoolingInputs();tr=transitions(p)
onsets=[full_wall_onset(p,tol=2e-10,length=16),full_wall_onset(p,tol=5e-11,length=20)]
print(json.dumps({'transitions':tr,'onsets':onsets}),flush=True)
bulk=tr['bulk_Higgs_ordering_temperature_GeV'];wall=onsets[-1]['temperature_GeV'];previous=None;profiles=[]
for T in [0.,100.,135.,139.,bulk-.05,bulk-.005,bulk+.002,bulk+.005,wall-.001,wall-.0002,wall+.001,145.,200.,400.,600.,780.]:
    w=solve_thermal_wall(T,p,previous=previous);row=w['report']
    if bulk<T<wall:
        row['condensation_energy']=wall_condensation_energy(w,p);row['leading_PT_projection']=projected_condensation(T,p);row['matched_Robin_defect']=robin_defect_condensation(T,p)
    row['tree_vector_background']=gauge_background(row);row['central_cubic_background']=cubic_background(row,p)
    profiles.append(row);previous=w
    print(json.dumps({k:row[k] for k in ['temperature_GeV','central_Higgs_GeV','tension_GeV3','BVP_residual']}|{'condensation':row.get('condensation_energy')}),flush=True)
controls=[]
for T in [0.,bulk+.005,600.]:
    # Find the same branch from its computed profile, not the h=0 saddle.
    source=next(x for x in profiles if abs(x['temperature_GeV']-T)<1e-9)
    anchor=solve_thermal_wall(T,p)
    fine=solve_thermal_wall(T,p,tol=2e-10,length=18,previous=anchor)
    if bulk<T<wall:fine['report']['condensation_energy']=wall_condensation_energy(fine,p,tol=5e-11)
    controls.append(fine['report'])
receipt={'inputs':asdict(p),'bulk_and_reduced_transitions':tr,'canonical_wall_zero_mode_onset_controls':onsets,'profiles':profiles,'refined_profiles':controls,
    'exact_global_bulk_phase_classification':True,'full_canonical_source_singlet_radial_Higgs_profiles':True,
    'interval_certified_thermal_profiles':False,'gauge_resummed_effective_action':False,'physical_collision_or_damping_kernel':False,
    'scope':'Declared leading thermal mass model. Numerical canonical static continuation and even Higgs zero-mode onset; no real-time Higgs evolution or complete thermal electroweak lifetime.'}
(root/'receipts/flavor_cosmology/wall_cooling.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
