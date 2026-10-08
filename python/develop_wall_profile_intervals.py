"""Generate an untrusted profile and independently check its interval certificate."""
from pathlib import Path
import json,hashlib
from perfectpower.wall_profile_intervals import generate_seed,check_seed

root=Path(__file__).resolve().parents[1]
p=root/'receipts/flavor_cosmology/wall_profile_interval_seed.json'
if not p.exists():p.write_text(json.dumps(generate_seed(),sort_keys=True,separators=(',',':'))+'\n')
seed=json.loads(p.read_text());report=check_seed(seed)
report['seed_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
q=root/'receipts/flavor_cosmology/wall_profile_intervals.json';q.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps(report,indent=2))
