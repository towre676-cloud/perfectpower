#!/usr/bin/env bash
set -euo pipefail
for name in FormulaTransport ArithmeticSimplifier PolynomialCapacity SemilinearCapacity SignedPowerCharts NativePowerRoots SemilinearPowerSearch; do
  lake env lean -s65536 "PerfectPower/$name.lean" -o ".lake/build/lib/lean/PerfectPower/$name.olean"
done
lake env lean audit/SemilinearCapacity.lean > /tmp/perfectpower-semilinear-axioms.log
lake env lean -s65536 audit/SemilinearExamples.lean > /tmp/perfectpower-semilinear-examples.log
python3 - <<'PY'
import re
from pathlib import Path
s=Path('/tmp/perfectpower-semilinear-axioms.log').read_text()+Path('/tmp/perfectpower-semilinear-examples.log').read_text()
rows=re.findall(r"'PerfectPower\.[^']+' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",s)
assert len(rows)==29,s
assert all(set(x.strip() for x in row.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'} for row in rows),s
print('Twenty-nine semilinear declarations: standard axioms only')
PY
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_semilinear_capacity.py
