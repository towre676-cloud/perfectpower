from __future__ import annotations
import json

def build_hard_equivalence_manifest(component_ledger_json, out_json):
    d=json.load(open(component_ledger_json))
    components=[]
    for s,cs in d['by_species'].items():
        for c in cs: components.append({'species':int(s),'members':c,'size':len(c)})
    out={'components':components,'component_count':len(components),'hard_negative_pairs':[[2,35],[159,160]],'positive_multiobject_components':[c['members'] for c in components if c['size']>1]}
    json.dump(out,open(out_json,'w'),indent=2); return out
