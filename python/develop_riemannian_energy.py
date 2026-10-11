"""Rebuild deterministic source-bound examples; does not claim Lean validation."""
from pathlib import Path
import json
from perfectpower.riemannian_energy import compile_energy_certificate,pullback
from fractions import Fraction as Q
out=Path('receipts/riemannian_energy');out.mkdir(parents=True,exist_ok=True)
base={'metric':[2,1,3],'vertices':[[0,0],[1,2],[3,-1]],'durations':[1,2]}
examples={
 'Detour':base,
 'Straight':{**base,'vertices':[[0,0],[1,2],[3,6]]},
 'Stationary':{**base,'vertices':[[2,3],[2,3],[2,3]]},
 'Rational':{'metric':[1,1,'1000001/1000000'],'vertices':[[0,0],['1/3','-2/5']],'durations':['7/11']},
 'Shear':{**base,'metric':pullback(tuple(map(Q,[3,1,2])),tuple(map(Q,[1,2,0,1]))),
          'transport':{'metric':[3,1,2],'linear':[1,2,0,1],'translation':['3/7',11]}},
 'Reflection':{**base,'metric':[2,-1,3],'transport':{'metric':[2,1,3],'linear':[-1,0,0,1],'translation':[5,7]}},
 'FirstJet':{**base,'derivatives':[[2,1,0],[0,-1,3]]},
 'FlatJet':{**base,'derivatives':[[0,0,0],[0,0,0]]},
}
summary={}
for name,p in examples.items():
    receipt,source=compile_energy_certificate(p,namespace=name)
    (out/(name+'.lean')).write_text(source)
    (out/(name+'.json')).write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
    summary[name]={'energy':receipt['energy'],'excess':receipt['excess'],'source_sha256':receipt['proof']['source_sha256']}
(out/'summary.json').write_text(json.dumps(summary,sort_keys=True,indent=2)+'\n')
print('Emitted',len(examples),'source-bound exact metric certificates; kernel validation is separate.')
