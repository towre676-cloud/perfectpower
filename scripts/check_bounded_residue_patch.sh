#!/usr/bin/env bash
set -euo pipefail
PYTHONPATH=python python3 python/develop_bounded_residue_patch.py
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_bounded_residue_patch.py
lake build PerfectPower.BoundedResiduePatch
proof_log=$(mktemp)
trap 'rm -f "$proof_log"' EXIT
lake env lean audit/BoundedResiduePatchAudit.lean | tee "$proof_log"
for source in receipts/bounded_residue_patch/*.lean; do
  lake env lean -s 65536 "$source" | tee -a "$proof_log"
done
python3 - "$proof_log" <<'PY'
import re,sys
text=open(sys.argv[1]).read()
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
assert len(sets)>=43, 'missing proof records'
for values in sets:
    assert {v.strip() for v in values.split(',') if v.strip()} <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
print(f'{len(sets)} declarations audited: standard axioms only')
PY
