#!/usr/bin/env bash
set -euo pipefail
lean_bin="${PERFECTPOWER_LEAN:-lean}"
chart_tmp=$(mktemp -d)
trap 'rm -rf "$chart_tmp"' EXIT
mkdir -p "$chart_tmp/PerfectPower"
"$lean_bin" -o "$chart_tmp/PerfectPower/EuclidMethods.olean" PerfectPower/EuclidMethods.lean
export LEAN_PATH="$chart_tmp${LEAN_PATH:+:$LEAN_PATH}"
"$lean_bin" -o "$chart_tmp/PerfectPower/LinearProductChart.olean" PerfectPower/LinearProductChart.lean
for name in Adjacent Six NegativeSlopes UnequalSlopes NoSolutions OddMidpoint Translated80Digits; do
  "$lean_bin" "receipts/linear_product/$name.lean"
done
python3 scripts/check_linear_product_rejections.py > receipts/linear_product/kernel-rejection.log
echo 'Both altered certificates rejected; see kernel-rejection.log.'
python3 scripts/record_linear_product_validation.py
