#!/usr/bin/env bash
# Exact algebra and saved certificates from the parallel geometry/deep-gems pushes.
set -euo pipefail
cd "$(dirname "$0")/.."
python3 python/build_parallel_lean.py
mkdir -p .lake/build/lib/lean/PerfectPower/Generated
# These existing dependencies do not need the expensive historical literal quartic catalogue.
for module in NativeNearSquare NativePolynomialSquare FastDivisors NativePolynomialRoots NativePowerRoots LinearPerturbation SquareLeadingQuartic; do
  lake env lean -s65536 "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
while IFS= read -r module; do
  lake env lean -s65536 "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done < <(python3 -c 'import json; print("\n".join(json.load(open("receipts/parallel_lean/inputs.json"))["modules"]))')
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean -s65536 audit/ParallelPush.lean > "$log"
python3 python/audit_parallel_lean.py "$log"
