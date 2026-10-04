#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower/Generated
PYTHONPATH=python python3 python/make_lean_orbit_recovery.py
lake env lean PerfectPower/OrbitRecovery.lean -o .lake/build/lib/lean/PerfectPower/OrbitRecovery.olean
lake env lean -s 65536 PerfectPower/Generated/OrbitRecovery.lean -o .lake/build/lib/lean/PerfectPower/Generated/OrbitRecovery.olean
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean audit/OrbitRecovery.lean | tee "$log"
python3 - "$log" <<'PY'
import re,sys
from pathlib import Path
s=Path(sys.argv[1]).read_text()
r=re.findall(r'depends on axioms: \[([^\]]*)\]',s)
assert len(r)+s.count('does not depend on any axioms')==12
for group in r:
    assert not ({x.strip() for x in group.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'})
PY
PYTHONPATH=python python3 -m unittest python.tests.test_operator_recovery
