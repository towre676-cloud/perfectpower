#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower/Tactic
for module in NativeNearSquare NativePolynomialSquare FastDivisors NativePolynomialRoots LinearPerturbation RungePolynomial Tactic/RungePolynomial; do
  lake env lean "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean -s 65536 audit/NativeRunge.lean | tee "$log"
python3 - "$log" <<'PY'
import re,sys
from pathlib import Path
text=Path(sys.argv[1]).read_text()
groups=re.findall(r'depends on axioms: \[([^\]]*)\]',text)
assert len(groups)==79, f'expected 79 declarations, found {len(groups)}'
allowed={'propext','Classical.choice','Quot.sound'}
for group in groups:
    assert not ({x.strip() for x in group.split(',') if x.strip()}-allowed), group
assert 'error:' not in text
print(f'Native Runge axiom audit passed: {len(groups)} declarations')
PY
