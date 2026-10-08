#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
PYTHONPATH=python python3 -m unittest python/tests/test_weil_spectral.py -v
lake build PerfectPower.WeilSpectral
lake env lean audit/WeilSpectral.lean
python3 - <<'PY'
import json,re,subprocess,tempfile,hashlib
from pathlib import Path
out=Path('receipts/weil_spectral');manifest=json.loads((out/'native_declarations.json').read_text())
allowed={'propext','Classical.choice','Quot.sound'}
def audit(text,expected):
    sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
    free=text.count('does not depend on any axioms')
    assert len(sets)+free==expected,(len(sets),free,expected)
    assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
    for record in sets:assert {x.strip() for x in record.split(',') if x.strip()}<=allowed
    return sorted({x.strip() for record in sets for x in record.split(',') if x.strip()})
p=subprocess.run(['lake','env','lean','audit/WeilSpectral.lean'],text=True,capture_output=True,check=True)
records=[{'kind':'generic','declarations':len(manifest['generic']),'axioms':audit(p.stdout,len(manifest['generic']))}]
with tempfile.TemporaryDirectory() as temp:
    for row in manifest['sources']:
        source=Path(row['path']);names=[n for n in manifest['native'] if n.startswith(f"PerfectPower.WeilSpectralExample{row['level']}.")]
        assert hashlib.sha256(source.read_bytes()).hexdigest()==row['sha256']
        path=Path(temp)/f"Audit{row['level']}.lean"
        path.write_text(source.read_text()+''.join(f'#print axioms {n}\n' for n in names))
        p=subprocess.run(['lake','env','lean',str(path)],text=True,capture_output=True)
        if p.returncode:raise RuntimeError(p.stdout+p.stderr)
        records.append({'kind':'native','level':row['level'],'source_sha256':row['sha256'],
                        'declarations':len(names),'axioms':audit(p.stdout,len(names))})
        print('Kernel checked native level',row['level'],flush=True)
result={'schema':'pp-weil-spectral-lean-audit/1','kernel_checked':True,'declarations':sum(r['declarations'] for r in records),
        'records':records,'scope':'Generic hypotheses and literal native levels only; not all-level orbit classification.'}
(out/'lean_audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['declarations'],'declarations: standard axioms only or axiom-free')
PY
