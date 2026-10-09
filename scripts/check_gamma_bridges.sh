#!/usr/bin/env bash
set -euo pipefail
lake build PerfectPower.FactorialUnit PerfectPower.LandauIntegral
audit_log=$(mktemp)
trap 'rm -f "$audit_log"' EXIT
lake env lean audit/FactorialGamma.lean > "$audit_log"
python3 - "$audit_log" <<'PY'
from pathlib import Path
import re
import sys
text = Path(sys.argv[1]).read_text()
names = re.findall(r"(?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text)
assert len(names) == 21, text
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert all({v.strip() for v in row.split(',') if v.strip()} <= allowed for row in names), text
assert 'sorry' not in text and 'ofReduceBool' not in text, text
print('Gamma bridge axiom audit: 21 declarations, standard axioms only')
PY
PERFECTPOWER_LEAN="${PERFECTPOWER_LEAN:-lean}" lake env python3 -m unittest discover -s python/tests -p 'test_checked_factorial_unit.py' -v
PERFECTPOWER_LEAN="${PERFECTPOWER_LEAN:-lean}" lake env python3 -m unittest discover -s python/tests -p 'test_checked_landau.py' -v
