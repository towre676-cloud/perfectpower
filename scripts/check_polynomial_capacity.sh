#!/usr/bin/env bash
set -euo pipefail
lake env lean -s65536 PerfectPower/PolynomialCapacity.lean -o .lake/build/lib/lean/PerfectPower/PolynomialCapacity.olean
lake env lean audit/PolynomialCapacity.lean > /tmp/perfectpower-polynomial-capacity-axioms.log
python3 - <<'PY'
import re
from pathlib import Path
s=Path('/tmp/perfectpower-polynomial-capacity-axioms.log').read_text()
rows=re.findall(r"'PerfectPower\.[^']+' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",s)
assert len(rows)==13,s
assert all(set(x.strip() for x in row.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'} for row in rows),s
print('Thirteen polynomial-capacity theorems: standard axioms only')
PY
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_polynomial_capacity.py
