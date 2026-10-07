#!/usr/bin/env bash
set -euo pipefail
PYTHONPATH=python python3 python/develop_residue_determinant.py
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_residue_determinant.py
lake build PerfectPower.IntegralKernelWitness PerfectPower.ResidueDeterminantCertificate
audit_log=$(mktemp)
trap 'rm -f "$audit_log"' EXIT
lake env lean audit/ResidueDeterminantAudit.lean | tee "$audit_log"
for source in receipts/residue_determinant/*.lean; do
  lake env lean -s 65536 "$source" | tee -a "$audit_log"
done
python3 - "$audit_log" <<'PY'
import re,sys
text=open(sys.argv[1]).read()
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
assert len(sets)>=40, 'missing proof records'
for values in sets:
    assert {v.strip() for v in values.split(',') if v.strip()} <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
print('focused axioms: standard only')
PY
