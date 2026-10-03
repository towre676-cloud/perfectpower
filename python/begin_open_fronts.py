"""Reproduce concrete residue experiments and the remaining analytic-premise inventory."""
import json
import re
from pathlib import Path
from orbit_lattice import allowed

ROOT=Path(__file__).resolve().parents[1]
records={
    'k11_weighted_lattice':allowed(-6,12,[(9337,1682,1144)],(16,3,2),8,-2),
    'negative63_class50':allowed(6,2,[(-5,0,1),(11,1,-2)],(4,0,0),8,4,
        plane=(0,1,1),extra_divisibility=[((0,0,1),4)]),
}
# enc 4 (17,4,-4) u v = (4u-17v,-4v,4v); these congruences are necessary only.
records['negative63_class50']['encoding']='(4u-17v,-4v,4v); plane w1+w2=0; 4|w0 and 4|w2'
records['analytic_premises']=[]
for module in ['Field756','D72Unit']:
    source=(ROOT/f'PerfectPower/Generated/{module}.lean').read_text()
    for match in re.finditer(r'def (matveev_\w+) : Prop :=\n(.*?)(?=\n\n)',source,re.S):
        records['analytic_premises'].append({'module':module,'name':match[1],'statement':match[2].strip(),
            'status':'named unproved analytic premise; residue exclusions do not remove it'})
(ROOT/'receipts/open_fronts.json').write_text(json.dumps(records,indent=2)+'\n')
print({name:(v['tested_residues'],len(v['allowed_residues'])) for name,v in records.items() if isinstance(v,dict)})
print('analytic premises',len(records['analytic_premises']))
