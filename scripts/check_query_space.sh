#!/usr/bin/env bash
set -euo pipefail
mkdir -p .lake/build/lib/lean/PerfectPower
for name in CoefficientPowerCharts RecurrenceDomains; do
  lake env lean -s65536 "PerfectPower/$name.lean" -o ".lake/build/lib/lean/PerfectPower/$name.olean"
done
lake env lean audit/QuerySpace.lean > /tmp/perfectpower-query-space-axioms.log
lake env lean -s65536 audit/QuerySpaceExamples.lean > /tmp/perfectpower-query-space-examples.log
python3 - <<'PY'
import re
from pathlib import Path
s=Path('/tmp/perfectpower-query-space-axioms.log').read_text()+Path('/tmp/perfectpower-query-space-examples.log').read_text()
rows=re.findall(r"'PerfectPower\.[^']+' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",s)
assert len(rows)==19,s
assert all(set(x.strip() for x in row.split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'} for row in rows),s
print('Nineteen coefficient-chart and recurrence declarations: standard axioms only')
PY
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_query_space_push.py
