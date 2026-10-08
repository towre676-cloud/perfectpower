"""Reproduce shared-factor intersection examples and exact populations."""
import json
from pathlib import Path
from perfectpower.residue_atlas import atlas_packet
from perfectpower.residue_atlas_product import product_packet
from perfectpower.residue_atlas_intersection import intersect_atlases, intersection_population

f = [[1,1,0],[-1,0,1]]
h = [[1,1,0],[1,0,1]]
cases = {
    'SharedDyadic': [atlas_packet(f,2,2), atlas_packet(h,2,3)],
    'SharedComposite': [product_packet(f,[[2,2],[3,1]]),product_packet(h,[[2,3],[5,1]])],
    'Incompatible': [atlas_packet([[1,1,0]],2,1),atlas_packet([[1,1,0],[-1,0,0]],2,1)],
}
bounds = [[-10**30,10**30],[-10**30,10**30]]
rows = {}
for name, inputs in cases.items():
    p = intersect_atlases(inputs)
    rows[name] = {'intersection':p,'bounds':bounds,'population':intersection_population(p,bounds)}
out = Path(__file__).resolve().parents[1]/'receipts'/'residue_atlas_intersection'
out.mkdir(parents=True,exist_ok=True)
(out/'corpus.json').write_text(json.dumps(rows,indent=2)+'\n')
print(json.dumps({n:{'modulus':r['intersection']['modulus'],'roots':len(r['intersection']['roots']),
                     'population':r['population']} for n,r in rows.items()},indent=2))
