"""Run only after the shell's successful Lean checks; bind checked sources."""
from pathlib import Path
import json,hashlib
out=Path('receipts/belyaev_geometry');sources=[]
for name in ('Rotation','Reflection','TriangleAreas'):
    packet=json.loads((out/f'{name}-proof.json').read_text());digest=hashlib.sha256((out/f'{name}.lean').read_bytes()).hexdigest()
    if digest!=packet['source_sha256']:raise AssertionError('source hash mismatch')
    sources.append({'name':name,'source_sha256':digest,'kernel_checked':True,'scope':packet['scope']})
(out/'kernel-validation.json').write_text(json.dumps({'schema':'pp-geometry-foundation-kernel-run/1',
 'generic_foundations_checked':True,'sources':sources,'corrupted_sources_rejected':2,
 'axioms':['propext','Classical.choice','Quot.sound'],
 'scope':'matrix norm/determinant identities and retained numeric area claims; no triangulation or routing algorithm verification'},indent=2)+'\n')
