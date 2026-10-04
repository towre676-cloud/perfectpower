#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean PerfectPower/SolutionChart.lean -o .lake/build/lib/lean/PerfectPower/SolutionChart.olean
lake env lean PerfectPower/NativeSquareChart.lean -o .lake/build/lib/lean/PerfectPower/NativeSquareChart.olean
audit_log=$(mktemp)
trap 'rm -f "$audit_log"' EXIT
lake env lean -s 65536 audit/SolutionChart.lean | tee "$audit_log"
python3 - "$audit_log" <<'PY'
import re
import sys
from pathlib import Path
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
text = Path(sys.argv[1]).read_text()
groups = re.findall(r'depends on axioms: \[([^\]]*)\]', text)
if len(groups) != 10:
    raise SystemExit('expected ten theorem axiom reports')
for group in groups:
    unexpected = {a.strip() for a in group.split(',') if a.strip()} - allowed
    if unexpected:
        raise SystemExit(f'unexpected axioms: {unexpected}')
PY
PYTHONPATH=python python3 -m unittest python.tests.test_solution_chart
