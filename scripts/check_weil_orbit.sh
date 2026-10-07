#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
PYTHONPATH=python python3 python/develop_weil_orbit.py
PYTHONPATH=python python3 -m unittest python/tests/test_weil_orbit.py -v
lake build PerfectPower.WeilOrbitSymmetry
proof_log=$(mktemp)
trap 'rm -f "$proof_log"' EXIT
lake env lean audit/WeilOrbitSymmetry.lean | tee "$proof_log"
python3 - "$proof_log" <<'PY'
from pathlib import Path
import re,sys
text=Path(sys.argv[1]).read_text()
sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
free=text.count('does not depend on any axioms')
expected=Path('audit/WeilOrbitSymmetry.lean').read_text().count('#print axioms')
assert len(sets)+free==expected
for record in sets:
    assert {x.strip() for x in record.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
print(f'{expected} declarations audited: standard axioms only or axiom-free')
PY
