#!/usr/bin/env python3
"""Publish source-bound geometric data from retained exact portfolio results."""
import gzip,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def export(root=ROOT):
 root=Path(root);request=root/'examples/planning/petersen_50_population.json';spec=json.loads(request.read_text())['specification'];results={};hashes={}
 for name in ('root','conditional'):
  path=root/f'receipts/planning/explorer/{name}.json.gz';raw=path.read_bytes();packet=json.loads(gzip.decompress(raw));hashes[path.relative_to(root).as_posix()]=hashlib.sha256(raw).hexdigest()
  assert packet['summary']['native_provenance']['source_sha256']==hashlib.sha256((root/'native/completion_planner.cpp').read_bytes()).hexdigest()
  point=packet['selection']['point'];costs=[sum(int(v['costs'][k])*int(x) for v,x in zip(spec['variables'],point)) for k in range(5)]
  assert [str(x) for x in costs]==packet['selection']['resource_use']
  assert sum(int(v['profit'])*int(x) for v,x in zip(spec['variables'],point))==int(packet['selection']['profit'])
  assert all(int(r.get('min',0))<=costs[k]<=int(r['max']) for k,r in enumerate(packet['specification']['resources']))
  if 'branches' in packet:assert sum(int(x['count']) for x in packet['branches'])==int(packet['conditional']['count'])
  results[name]={k:packet[k] for k in ('action','specification','summary','selection','conditional','branches','input_sha256') if k in packet}
 data={'schema':'pp-portfolio-geometry/1','model':{'specification':spec,'source_sha256':hashlib.sha256(request.read_bytes()).hexdigest()},'results':results,'receipt_hashes':hashes,'scope':'Retained exact engine results; geometric projections do not certify feasibility or enumerate the full population.'}
 out=root/'web/portfolio-geometry/data.json';out.write_text(json.dumps(data,sort_keys=True,indent=2)+'\n')
 receipt={'schema':data['schema'],'input_sha256':data['model']['source_sha256'],'retained_receipt_hashes':hashes,'data_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'resource_sum_replay':'pass','objective_sum_replay':'pass','branch_identity':'pass','original_projects':len(spec['variables'])}
 (root/'receipts/planning/explorer/geometry.json').write_text(json.dumps(receipt,indent=2)+'\n');return receipt
if __name__=='__main__':print(json.dumps(export()))
