#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for module in SquareLeadingQuartic QuarticCutoff Tactic/SquareLeadingQuartic Generated/RepunitQuartic; do
  lake env lean "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
log=$(mktemp)
emitted=$(mktemp --suffix=.lean)
trap 'rm -f "$log" "$emitted"' EXIT
lake env lean -s 65536 audit/SquareLeadingQuartic.lean | tee "$log"
PYTHONPATH=python python3 -m perfectpower lean --coeff=1,1,1,1,1 --d=2 --name=emitted_repunit > "$emitted"
lake env lean -s 65536 "$emitted" | tee -a "$log"
python3 - "$log" <<'PY'
import re,sys
from pathlib import Path
s=Path(sys.argv[1]).read_text()
r=re.findall(r'depends on axioms: \[([^\]]*)\]',s)
assert len(r)==10
for group in r:
    assert not ({x.strip() for x in group.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'})
PY
PYTHONPATH=python python3 -m unittest python.tests.test_linear_perturbation
