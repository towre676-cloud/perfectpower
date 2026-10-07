#!/usr/bin/env bash
set -euo pipefail
PYTHONPATH=python python3 python/develop_residue_atlas_product.py
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_residue_atlas_product.py
PYTHONPATH=python python3 python/crosscheck_residue_atlas_product.py
lake build PerfectPower.ResidueAtlasCRT
proof_log=$(mktemp)
trap 'rm -f "$proof_log"' EXIT
lake env lean audit/ResidueAtlasCRTAudit.lean | tee "$proof_log"
for source in receipts/residue_atlas_product/*.lean; do
  lake env lean -s 65536 "$source" | tee -a "$proof_log"
done
python3 - "$proof_log" <<'PY'
import re,sys
from pathlib import Path
text=Path(sys.argv[1]).read_text()
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
free=text.count('does not depend on any axioms')
expected=Path('audit/ResidueAtlasCRTAudit.lean').read_text().count('#print axioms')+sum(p.read_text().count('#print axioms') for p in Path('receipts/residue_atlas_product').glob('*.lean'))
assert len(sets)+free==expected, 'missing proof records'
for values in sets:
    assert {v.strip() for v in values.split(',') if v.strip()} <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
print(f'{len(sets)+free} declarations audited: standard axioms only or axiom-free')
PY
