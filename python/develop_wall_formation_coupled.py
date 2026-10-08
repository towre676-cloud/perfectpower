"""Coupled OU paths for statistical timestep sensitivity of formed wall lengths."""
from pathlib import Path
import json
from perfectpower.wall_kibble_zurek import coupled_timestep_check
checks=[]
for dt in [.1,.05]:
    a=coupled_timestep_check(128,coarse_dt=dt);checks.append(a);print(json.dumps(a),flush=True)
root=Path(__file__).resolve().parents[1]
(root/'receipts/flavor_cosmology/wall_formation_coupled_timestep.json').write_text(json.dumps({'checks':checks},sort_keys=True,indent=2)+'\n')
