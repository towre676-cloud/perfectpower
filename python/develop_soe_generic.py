"""Reproduce general finite SOE kernel receipts (run in configured lake env)."""
import json
from pathlib import Path
from perfectpower.checked_soe import compile_soe, accept_soe
ROOT=Path(__file__).resolve().parents[1]
MODELS=[
 {'observations':[0,0,1],'actions':{'advance':[1,2,0],'stop':[None,1,2]}},
 {'observations':[0,0,0,1],'actions':{'a':[0,1,3,3],'b':[0,3,2,3]}},
 {'observations':[{'label':'λ'},{'label':'λ'},True,1], 'actions':{'disabled':[None,None,2,3],'cycle':[1,0,3,2],'reset':[0,0,0,0]}},
]
def main():
 out=ROOT/'receipts/soe_generic';out.mkdir(exist_ok=True)
 lines=['import PerfectPower.SOESemantics'];receipts=[]
 for i,model in enumerate(MODELS):
  c=compile_soe(model);r=accept_soe(model)
  if not r['accepted']:raise RuntimeError(r)
  lines.append(c['lean'].removeprefix('import PerfectPower.SOESemantics\n'));receipts.append({'model':model,'result':r})
 (ROOT/'PerfectPower/Generated/SOEGenericPackets.lean').write_text('\n'.join(lines))
 (out/'kernel_acceptance.json').write_text(json.dumps(receipts,indent=2)+'\n')
 print('Kernel accepted three source-bound models with 3/4 states and 2/3 actions')
if __name__=='__main__':main()
