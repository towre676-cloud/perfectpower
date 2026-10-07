#!/usr/bin/env bash
set -euo pipefail
mkdir -p .lake/build/lib/lean/PerfectPower receipts/dresden
# Compile dependencies sequentially in the pinned project environment.
for name in GeneralCRT ResiduePopulation FiniteDomainCertificate PolynomialSourceSemantics DresdenCalendar; do
  lake env lean -s65536 "PerfectPower/$name.lean" -o ".lake/build/lib/lean/PerfectPower/$name.olean"
done
lake env lean -s65536 audit/DresdenCalendar.lean > receipts/dresden/lean-axioms.log
python3 - <<'PY'
from pathlib import Path
import hashlib,json,re,subprocess
log=Path('receipts/dresden/lean-axioms.log').read_text()
rows=re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",log)
assert len(rows)==22,log
allowed={'propext','Classical.choice','Quot.sound'}
for name,axioms in rows:
    assert set(a.strip() for a in axioms.split(',') if a.strip())<=allowed,(name,axioms)
paths=['PerfectPower/DresdenCalendar.lean','audit/DresdenCalendar.lean','PerfectPower/GeneralCRT.lean','PerfectPower/ResiduePopulation.lean','PerfectPower/FiniteDomainCertificate.lean','PerfectPower/PolynomialSourceSemantics.lean']
receipt={'schema':'dresden-lean-proof-status/1','toolchain':'Lean 4.20.0','lean_version':subprocess.check_output(['lake','env','lean','--version'],text=True).strip(),'status':'kernel_checked','library_theorems':19,'audit_examples':3,'declarations':[{'name':n,'axioms':[a.strip() for a in ax.split(',') if a.strip()]}for n,ax in rows],'source_sha256':{p:hashlib.sha256(Path(p).read_bytes()).hexdigest()for p in paths},'scope':'Exact model mathematics: polynomial and Boolean pullback, original coordinates, finite counts and rank, CRT, canonical Long Count, restart activation, affine drift and lunar window counts','not_formalized':['General Sturm completeness','JSON parsing','Python and JavaScript execution','Historical source readings','Physical astronomical visibility']}
Path('receipts/dresden/lean-proof-status.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('PASS: 19 Dresden library theorems and 3 concrete audit examples; standard axioms only.')
PY
