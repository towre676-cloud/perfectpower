#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower/Tactic receipts/lean_backlog
for module in NativeNearSquare NativePolynomialSquare FastDivisors LinearPerturbation SquareLeadingQuartic QuarticCutoff Tactic/SquareLeadingQuartic; do
  lake env lean "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
lake env lean -s 65536 audit/QuarticCutoff.lean > receipts/lean_backlog/quartic_axioms.log
