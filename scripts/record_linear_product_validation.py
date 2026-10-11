"""Record source hashes only after the shell's successful Lean checks."""
import hashlib,json
from pathlib import Path
names=('Adjacent','Six','NegativeSlopes','UnequalSlopes','NoSolutions','OddMidpoint','Translated80Digits')
out=Path('receipts/linear_product');sources=[]
for name in names:
    digest=hashlib.sha256((out/f'{name}.lean').read_bytes()).hexdigest()
    packet=json.loads((out/f'{name}-proof.json').read_text())
    if digest!=packet['source_sha256']:raise AssertionError('proof source hash mismatch')
    sources.append({'name':name,'source_sha256':digest,'kernel_checked':True,
                    'theorem_scope':'all signed integer pairs for the original supplied linear factors'})
(out/'kernel-validation.json').write_text(json.dumps({'schema':'pp-linear-product-kernel-run/1',
    'generic_completeness_checked':True,'sources':sources,'corrupted_sources_rejected':2,
    'axioms':['propext','Classical.choice','Quot.sound'],
    'scope':'retained emitted sources and generic chart; does not assert verification of Python execution'},indent=2)+'\n')
