#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower/Generated .lake/build/lib/lean/PerfectPower/Tactic
PYTHONPATH=python python3 python/make_lean_linear_catalogue.py
for module in LinearPerturbation Tactic/LinearPerturbation Generated/LinearCatalogue; do
  lake env lean -s 65536 "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean -s 65536 audit/LinearPerturbation.lean | tee "$log"
python3 - "$log" <<'PY'
import re,sys
from pathlib import Path
s=Path(sys.argv[1]).read_text()
r=re.findall(r'depends on axioms: \[([^\]]*)\]',s)
assert len(r)+s.count('does not depend on any axioms')==428
for group in r:
    assert not ({x.strip() for x in group.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'})
PY
PYTHONPATH=python python3 -m unittest python.tests.test_linear_perturbation
