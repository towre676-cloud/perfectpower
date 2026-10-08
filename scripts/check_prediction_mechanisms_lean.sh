#!/usr/bin/env bash
set -euo pipefail
mkdir -p .lake/build/lib/lean/PerfectPower receipts/m22_interactions
for name in FactorAddresses FlavorRG SpectralMoments WeilOldLevel FlavorRGCensus WeightedBlockAddresses SpectralTrace; do
  lake env lean -s65536 "PerfectPower/$name.lean" -o ".lake/build/lib/lean/PerfectPower/$name.olean"
done
lake env lean -s65536 audit/PredictionMechanisms.lean > receipts/m22_interactions/prediction-mechanisms-axioms.log
python3 - <<'PY'
from pathlib import Path
import hashlib,json,re,subprocess
modules=['FactorAddresses','FlavorRG','SpectralMoments','WeilOldLevel','FlavorRGCensus','WeightedBlockAddresses','SpectralTrace']
namespaces={'FlavorRGCensus':'FlavorRG','WeightedBlockAddresses':'FactorAddresses','SpectralTrace':'SpectralMoments'}
paths=['PerfectPower/'+n+'.lean' for n in modules]+['audit/PredictionMechanisms.lean']
expected=[]
for n in modules:
    expected += ['PerfectPower.'+namespaces.get(n,n)+'.'+x for x in re.findall(r'^(?:@\[[^\]]+\] )?theorem (\w+)',Path('PerfectPower/'+n+'.lean').read_text(),re.M)]
log=Path('receipts/m22_interactions/prediction-mechanisms-axioms.log').read_text()
rows=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",log)
assert [n for n,_ in rows]==expected,log
allowed={'propext','Classical.choice','Quot.sound'}
declarations=[]
for name,axioms in rows:
    ax=[a.strip() for a in axioms.split(',') if a.strip()]
    assert set(ax)<=allowed,(name,ax)
    declarations.append({'name':name,'axioms':ax})
receipt={'schema':'pp-prediction-mechanisms-lean/1','status':'kernel_checked',
    'lean_version':subprocess.check_output(['lake','env','lean','--version'],text=True).strip(),
    'declarations':declarations,'theorem_count':len(rows),
    'source_sha256':{p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in paths},
    'scope':'Seven focused modules, not a whole-repository build',
    'not_formalized':['Feynman-diagram derivation','existence and physical identification of spectral frames','JSON execution','CRT chart traversal','Fourier/chirp intertwining','observed CKM and alpha(0) prediction']}
Path('receipts/m22_interactions/prediction-mechanisms-lean.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(f'PASS: {len(rows)} theorems in seven modules; standard axioms only.')
PY
