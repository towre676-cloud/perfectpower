#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONPATH=python
lake build PerfectPower.IntegerValuedPowerCharts PerfectPower.BranchingResidueCharts PerfectPower.UnorderedWeightedDeterminant
python -m unittest python.tests.test_arithmetic_chart_pipeline python.tests.test_integer_valued_polynomial python.tests.test_residue_atlas python.tests.test_residue_atlas_product python.tests.test_residue_atlas_intersection_factored python.tests.test_residue_determinant python.tests.test_bounded_residue_patch
python python/develop_arithmetic_chart_pipeline.py
python python/crosscheck_arithmetic_chart_pipeline.py
task_logs="$(mktemp -d)"
trap 'rm -rf "$task_logs"' EXIT
lake env lean audit/ArithmeticChartPipelineAudit.lean > "$task_logs/GenericAudit.log" 2>&1
for task_source in receipts/arithmetic_chart_pipeline/*.lean; do
  task_name="$(basename "$task_source" .lean)"
  lake env lean "$task_source" > "$task_logs/$task_name.log" 2>&1
done
python - "$task_logs" <<'PY'
import pathlib,re,sys
logs=list(pathlib.Path(sys.argv[1]).glob('*.log'))
count=0
for log in logs:
    text=log.read_text()
    if 'error:' in text or 'sorryAx' in text or 'Lean.ofReduceBool' in text:
        raise SystemExit('failed proof or nonstandard axiom in '+log.name)
    count+=len(re.findall('depends on axioms:',text))
print('Kernel declarations audited:',count)
PY
