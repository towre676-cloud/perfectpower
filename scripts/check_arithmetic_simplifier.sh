#!/usr/bin/env bash
set -euo pipefail
lake env lean PerfectPower/FormulaTransport.lean -o .lake/build/lib/lean/PerfectPower/FormulaTransport.olean
lake env lean PerfectPower/ArithmeticSimplifier.lean -o .lake/build/lib/lean/PerfectPower/ArithmeticSimplifier.olean
lake env lean PerfectPower/WoodburyRepair.lean -o .lake/build/lib/lean/PerfectPower/WoodburyRepair.olean
lake env lean PerfectPower/WitnessResolvent.lean -o .lake/build/lib/lean/PerfectPower/WitnessResolvent.olean
lake env lean audit/ArithmeticSimplifierExamples.lean > /tmp/perfectpower-simplifier-examples.log
lake env lean audit/ArithmeticSimplifier.lean > /tmp/perfectpower-simplifier-axioms.log
python3 - <<'PY'
import re
from pathlib import Path
s=Path('/tmp/perfectpower-simplifier-axioms.log').read_text()+Path('/tmp/perfectpower-simplifier-examples.log').read_text()
rows=re.findall(r"depends on axioms: \[([^]]*)\]",s)
assert len(re.findall(r"'PerfectPower\.(?:ArithmeticSimplifier(?:Examples)?|WoodburyRepair|WitnessResolvent)\.[^']+'",s))==19, s
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(x.strip() for x in row.split(',') if x.strip())<=allowed for row in rows),s
print('Nineteen simplifier and parallel-repair theorems: standard axioms only')
PY
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_simplifier.py
