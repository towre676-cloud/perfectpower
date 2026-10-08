"""Real-time formation ensembles and separate numerical controls."""
from pathlib import Path
from dataclasses import replace
import json,time
import numpy as np
from perfectpower.wall_kibble_zurek import FormationInputs,simulate,summarize_run,scaling_fit

root=Path(__file__).resolve().parents[1]
base=FormationInputs();runs=[];snapshots=[]
for q in [64.,128.,256.,512.]:
    started=time.monotonic();r=simulate(q,inputs=base);runs.append(summarize_run(r));snapshots.append(r['first_replica_snapshots'][-2])
    print(json.dumps({'quench':q,'seconds':time.monotonic()-started,'final':runs[-1]['ensemble_summary'][-1]}),flush=True)
controls=[]
for label,p in [('half_dt',replace(base,dt=.05)),('half_spacing',replace(base,nodes=256,replicas=6)),('double_box',replace(base,nodes=256,length=256,replicas=6)),('smaller_noise',replace(base,noise_temperature=.0000025))]:
    started=time.monotonic();r=simulate(128,inputs=p);controls.append({'label':label,**summarize_run(r)})
    print(json.dumps({'control':label,'seconds':time.monotonic()-started,'at5':controls[-1]['ensemble_summary'][-2]}),flush=True)
receipt={'primary_runs':runs,'numerical_and_bath_controls':controls,
    'scaling_fits':[scaling_fit(runs,time_over_hat=t) for t in [3.,4.,5.,6.]],
    'reduced_source_dynamics':True,'declared_Model_A_bath_is_matched_to_particle_physics':False,
    'full_three_field_or_gauge_real_time_evolution':False,'cosmological_network_prediction':False,
    'scope':'Real stochastic 2D lattice source-wall formation with exact quartic and linear-OU split steps. The Gaussian valley is eliminated and the Higgs-restored branch is checked at the declared mean-field temperature range. Cutoff, noise, friction and quench are inputs; no continuum critical renormalization, expanding universe, GW production or complete nonlinear localized-mode lifetime.'}
(root/'receipts/flavor_cosmology/wall_kibble_zurek.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
np.savez_compressed(root/'receipts/flavor_cosmology/wall_kibble_zurek_snapshots.npz',fields=np.array(snapshots),quenches=np.array([64,128,256,512]))
print(json.dumps(receipt['scaling_fits'],indent=2),flush=True)
