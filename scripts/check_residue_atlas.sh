#!/usr/bin/env bash
set -euo pipefail
PYTHONPATH=python python3 python/develop_residue_atlas.py
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_residue_atlas.py
PYTHONPATH=python python3 python/crosscheck_residue_atlas.py
lake build PerfectPower.ResidueAtlas
proof_log=$(mktemp)
trap 'rm -f "$proof_log"' EXIT
lake env lean audit/ResidueAtlasAudit.lean | tee "$proof_log"
for source in receipts/residue_atlas/*.lean; do
  lake env lean -s 65536 "$source" | tee -a "$proof_log"
done
python3 - "$proof_log" <<'PY'
import re,sys
text=open(sys.argv[1]).read()
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
assert len(sets)>=100, 'missing proof records'
for values in sets:
    assert {v.strip() for v in values.split(',') if v.strip()} <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
print(f'{len(sets)} declarations audited: standard axioms only')
PY
