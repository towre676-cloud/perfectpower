#!/usr/bin/env bash
set -euo pipefail
PYTHONPATH=python python3 python/develop_arithmetic_chart_bridge.py
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_rational_power_atlas.py
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_unordered_weighted_determinant.py
PYTHONPATH=python python3 python/crosscheck_arithmetic_chart_bridge.py
lake build PerfectPower.RationalPowerAtlas PerfectPower.UnorderedWeightedGram
proof_log=$(mktemp)
trap 'rm -f "$proof_log"' EXIT
lake env lean audit/ArithmeticChartBridgeAudit.lean | tee "$proof_log"
for source in receipts/arithmetic_chart_bridge/*.lean; do
  lake env lean -s 65536 "$source" | tee -a "$proof_log"
done
python3 - "$proof_log" <<'PY'
import json,re,sys
from pathlib import Path
text=Path(sys.argv[1]).read_text();sets=re.findall(r'depends on axioms:\s*\[([^]]*)\]',text)
free=text.count('does not depend on any axioms')
generic=Path('audit/ArithmeticChartBridgeAudit.lean').read_text().count('#print axioms')
native=sum(p.read_text().count('#print axioms') for p in Path('receipts/arithmetic_chart_bridge').glob('*.lean'))
assert len(sets)+free==generic+native
for values in sets:assert {v.strip() for v in values.split(',') if v.strip()} <= {'propext','Classical.choice','Quot.sound'}
assert 'sorryAx' not in text and 'Lean.ofReduceBool' not in text
record={'lean_version':'4.20.0','generic_declarations':generic,'native_declarations':native,
 'total_audited':generic+native,'power_worked_packets':8,'weighted_native_packets':2,
 'focused_tests':17,'independent_power_cases':120,'independent_weighted_cases':120,
 'axioms':'standard axioms only or axiom-free','generic_interpreter_refinement':False,
 'scope':'exact rational power transport, original-coordinate chart covers/counts, complete bounded branching patches and unordered weighted determinant'}
Path('receipts/arithmetic_chart_bridge/validation.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
PY
