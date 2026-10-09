#!/usr/bin/env bash
set -euo pipefail
lake build PerfectPower.DivisorPopulation PerfectPower.PellFamily PerfectPower.AdditionalMordellPopulations PerfectPower.MordellDescentMask
out=$(mktemp)
trap 'rm -f "$out"' EXIT
lake env lean audit/FamilyPopulation.lean > "$out"
python3 - "$out" <<'PY'
from pathlib import Path
import re,sys
s=Path(sys.argv[1]).read_text();rows=re.findall(r'(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)',s)
assert len(rows)==25,s
assert all(set(a.strip() for a in row.split(',') if a.strip()) <= {'propext','Classical.choice','Quot.sound'} for row in rows),s
assert 'sorry' not in s and 'ofReduceBool' not in s,s
print('Twenty-five family source theorems audited')
PY
PERFECTPOWER_LEAN="${PERFECTPOWER_LEAN:-lean}" lake env python3 -m unittest discover -s python/tests -p 'test_checked_family_push.py' -v
