#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower
for module in BranchedGeometry IntegerLiftRecovery; do
  lake env lean -s 65536 "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
lake env lean audit/BranchedGeometry.lean > receipts/branched_geometry/lean_axioms.log
lake env lean -s 65536 receipts/branched_geometry/GeometryCells.lean > receipts/branched_geometry/lean_cell_checks.log
lake env lean -s 65536 receipts/branched_geometry/IntegerLiftPackets.lean > receipts/branched_geometry/lean_lift_packet_checks.log
python3 - <<'PY'
from pathlib import Path
import re
for filename,count in [('lean_axioms.log',17),('lean_cell_checks.log',12),('lean_lift_packet_checks.log',5)]:
    text=(Path('receipts/branched_geometry')/filename).read_text()
    groups=re.findall(r'depends on axioms: \[([^\]]*)\]',text)
    assert len(groups)==count,(filename,len(groups))
    for group in groups:
        assert not ({x.strip() for x in group.split(',') if x.strip()}-{'propext','Classical.choice','Quot.sound'})
PY
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_branched_geometry.py -v
