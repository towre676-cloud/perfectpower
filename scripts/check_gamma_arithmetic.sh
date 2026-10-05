#!/usr/bin/env bash
set -euo pipefail
for name in GammaArithmetic HypergeometricTransport IntegralOutputTransport; do
  lake env lean -s65536 "PerfectPower/$name.lean" -o ".lake/build/lib/lean/PerfectPower/$name.olean"
done
lake env lean audit/GammaArithmetic.lean > /tmp/perfectpower-gamma-axioms.log
python3 - <<'PY'
import re
from pathlib import Path
s=Path('/tmp/perfectpower-gamma-axioms.log').read_text()
rows=re.findall(r"'PerfectPower\.[^']+' (?:does not depend on any axioms|depends on axioms: \[([^]]*)\])",s)
assert len(rows)==20,s
allowed={'propext','Classical.choice','Quot.sound'}
assert all(set(x.strip() for x in row.split(',') if x.strip())<=allowed for row in rows),s
print('Twenty Gamma and parallel transport theorems: standard axioms only')
PY
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_gamma_arithmetic.py
PYTHONPATH=python python3 python/benchmark_gamma.py --out /tmp/perfectpower-gamma-corpus.json
