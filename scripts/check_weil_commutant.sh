#!/usr/bin/env bash
set -euo pipefail
PYTHONPATH=python python3 python/develop_weil_commutant.py
python3 python/reconcile_mordell_frontier.py
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_weil_commutant.py
lake build PerfectPower.WeilCRT
proof_log=$(mktemp)
trap 'rm -f "$proof_log"' EXIT
lake env lean audit/WeilCRT.lean | tee "$proof_log"
python3 - "$proof_log" <<'PY'
from pathlib import Path
import re,sys
text=Path(sys.argv[1]).read_text();sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
free=text.count('does not depend on any axioms');expected=Path('audit/WeilCRT.lean').read_text().count('#print axioms')
assert len(sets)+free==expected
for record in sets:assert {x.strip() for x in record.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
print(f'{expected} declarations audited: standard axioms only or axiom-free')
PY
