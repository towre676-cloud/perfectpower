"""Recompute original Forge residual ranks without mutating vendored files."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
src=ROOT/'vendor/forge/scripts/build_dual_hankel_semantics_v26.py'
ns={'__file__':str(src)}
# Execute original function definitions, excluding its output-writing driver.
exec(compile(src.read_text().split('specs={')[0],str(src),'exec'),ns)
rows={}
for name,D in [('sensor_d8_m12_padic.json',8),('paley_d8_m12_padic.json',8),('sensor_d9_p1_padic.json',9),('paley_d9_p1_padic.json',9)]:
 path=ROOT/'vendor/forge/DATA/RELATION/TASK_SELECTED_WORD_PROGRAMS_V23'/name
 _,words,nums=ns['load_program'](path,D)
 modes=[]
 for p in ns['PRIMES']:
  modes.append({'prime':p,'algebra_build':ns['profile'](words,nums,D,p,False),'column_execution':ns['profile'](words,nums,D,p,True)})
 for mode in ['algebra_build','column_execution']:
  assert all(m[mode]==modes[0][mode] for m in modes)
 rows[name]=modes
 print(name,modes[0]['algebra_build']['primitive_calls'],modes[0]['column_execution']['primitive_calls'],flush=True)
(ROOT/'receipts/forge_directional_recomputed.json').write_text(json.dumps(rows,indent=2))
