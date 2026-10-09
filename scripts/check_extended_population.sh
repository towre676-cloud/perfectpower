#!/usr/bin/env bash
set -euo pipefail
lake build PerfectPower.PolynomialFibre PerfectPower.GlobalMordellMinus4Population PerfectPower.PellPopulation
out=$(mktemp)
trap 'rm -f "$out"' EXIT
lake env lean audit/ExtendedPopulation.lean > "$out"
python3 - "$out" <<'PY'
from pathlib import Path
import re,sys
t=Path(sys.argv[1]).read_text()
r=re.findall(r'(?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)',t)
assert len(r)==14,t
assert all({a.strip() for a in row.split(',') if a.strip()} <= {'propext','Classical.choice','Quot.sound'} for row in r),t
assert 'sorry' not in t and 'ofReduceBool' not in t,t
print('Fourteen nonlinear, Mordell-minus-four and Pell source theorems audited')
PY
PERFECTPOWER_LEAN="${PERFECTPOWER_LEAN:-lean}" lake env python3 -m unittest discover -s python/tests -p 'test_checked_extended_population.py' -v
