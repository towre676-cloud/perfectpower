#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
for module in IntegralPullback CoveringMaps TargetDecoder; do
  lake env lean "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean audit/RecoveredBridges.lean | tee "$log"
python3 - "$log" <<'PY'
import re, sys
from pathlib import Path
s=Path(sys.argv[1]).read_text()
r=re.findall(r'depends on axioms: \[([^\]]*)\]',s)
assert len(r)+s.count('does not depend on any axioms')==8
for group in r:
    assert not ({x.strip() for x in group.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'})
PY
