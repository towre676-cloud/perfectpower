#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower/Tactic
for module in NativeNearSquare NativePolynomialSquare FastDivisors NativePolynomialRoots LinearPerturbation RungePolynomial NativePowerRoots RungePower Tactic/RungePower; do
  lake env lean "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean -s 65536 audit/NativeRungePower.lean | tee "$log"
python3 - "$log" <<'PY'
import re,sys
from pathlib import Path
text=Path(sys.argv[1]).read_text()
groups=re.findall(r'depends on axioms: \[([^\]]*)\]',text)
assert len(groups)==124, f'expected 124 declarations, found {len(groups)}'
allowed={'propext','Classical.choice','Quot.sound'}
for group in groups:
    assert not ({x.strip() for x in group.split(',') if x.strip()}-allowed), group
assert 'error:' not in text
print(f'Native Runge power axiom audit passed: {len(groups)} declarations')
PY
