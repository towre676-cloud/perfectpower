from pathlib import Path
import sys,json
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'src'));sys.path.insert(0,str(ROOT/'vendor/forge'))
from arithmetic import *
from modules.wilson_algebra.task_designed_word_programs_v24 import exact_verify,SELECTED
from modules.wilson_algebra.task_signature_compiler_v22 import TaskSignatureCompiler
out=ROOT/'receipts'
forge={name:exact_verify(name) for name in SELECTED}
assert all(r['hecke_exact'] and r['native_mask_exact'] for r in forge.values())
compiler=TaskSignatureCompiler(ROOT/'vendor/forge');geometry=compiler.geometry()
(out/'forge_reproduced.json').write_text(json.dumps({'exact_rational_programs':forge,'signature_geometry':geometry},indent=2))
# Derived arithmetic family, NOT the unavailable 316-branch workload.
# Cube coefficient forms q*a^3+3p*a^2*b-3Dq*a*b^2-pD*b^3.
forms=[]
for D in range(1,101):
 for p,q in [(1,1),(2,1),(1,2)]:
  F=(q,3*p,-3*D*q,-p*D)
  for T in [(1,0,0,1),(0,1,1,0),(-1,0,0,1),(1,1,0,1)]:
   cert=transport_certificate(F,1,T);assert check_transport(cert)
   U,V=bound_transport(T,12,12)
   # verify each transformed point against source equation; bounded only
   G=tuple(cert['target']);pts=bounded_solutions(G,1,12,12)
   assert all(evaluate(F,*apply(T,z))==1 for z in pts)
   forms.append({'D':D,'p':p,'q':q,'certificate':cert,'transformed_box_solutions':[list(z) for z in pts],'source_absolute_bounds':[U,V]})
(out/'derived_transport_experiments.json').write_text(json.dumps({'scope':'1200 transformations in an explicitly derived family; not actual Mordell branch certificates','experiments':forms},indent=2))
local=[]
for D in range(1,101):
 F=(1,3,-3*D,-D)
 checks=[local_obstruction(F,1,m) for m in [2,3,4,5,7,8,9,13,16,27]]
 local.append({'D':D,'checks':checks})
(out/'derived_local_experiments.json').write_text(json.dumps({'scope':'derived coefficient forms only; no claim about a source curve','rows':local},indent=2))
print('Exact Forge programs:',len(forge),'transport certificates:',len(forms),'finite modular checks:',sum(len(r['checks']) for r in local))
