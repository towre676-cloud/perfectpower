"""Discover EXACT edges from normalized actual Thue obligations.
Input JSON: [{"form":[c0,c1,c2,c3],"rhs":M,"restrictions":{},...}]
The existing repo exporter must supply these from its own authoritative receipt.
No guessed ledger keys or whole-GL2 canonical classification.
"""
from pathlib import Path
import argparse,json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent/'src'))
from arithmetic import *
p=argparse.ArgumentParser();p.add_argument('input');p.add_argument('--out',default='receipts/actual_transport_graph.json');p.add_argument('--height',type=int,default=2);a=p.parse_args()
rows=json.loads(Path(a.input).read_text())
for r in rows:
 if len(r['form'])!=4 or not all(type(c) is int for c in r['form']) or type(r['rhs']) is not int:raise ValueError('integer cubic coefficients and rhs required')
edges=discover_edges(rows,a.height);assert all(check_transport(e['certificate']) for e in edges)
sharing=intern_obligations(rows)
payload={'scope':'bounded matrix discovery with exact edge verification','height':a.height,'edges':edges,'exact_sharing':sharing,'global_canonicalization_claim':False}
Path(a.out).parent.mkdir(parents=True,exist_ok=True);Path(a.out).write_text(json.dumps(payload,indent=2));print('edges',len(edges),'exact unique obligations',sharing['unique_count'])
