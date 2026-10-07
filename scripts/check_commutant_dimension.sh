#!/usr/bin/env bash
set -euo pipefail
lake build PerfectPower.WeilTensorDimension
proof_log=$(mktemp)
trap 'rm -f "$proof_log"' EXIT
lake env lean audit/CommutantDimension.lean | tee "$proof_log"
python3 - "$proof_log" <<'PY'
from pathlib import Path
import re,sys
text=Path(sys.argv[1]).read_text();sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
free=text.count('does not depend on any axioms');expected=Path('audit/CommutantDimension.lean').read_text().count('#print axioms')
assert len(sets)+free==expected
for record in sets:assert {x.strip() for x in record.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
print(f'{expected} new declarations audited: standard axioms only or axiom-free')
PY
