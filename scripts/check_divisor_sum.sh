#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower/Tactic .lake/build/lib/lean/PerfectPower/Generated
for module in NativeNearSquare NativePolynomialSquare FastDivisors LinearPerturbation Tactic/LinearPerturbation SquareLeadingQuartic QuarticCutoff Tactic/SquareLeadingQuartic Generated/RepunitQuartic; do
  lake env lean -s 65536 "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
mkdir -p .lake/build/lib/lean/PerfectPower
lake env lean PerfectPower/DivisorSum.lean -o .lake/build/lib/lean/PerfectPower/DivisorSum.olean
lake env lean audit/DivisorSum.lean
python3 scripts/check_divisor_sum_catalogue.py "$@"
PYTHONPATH=python python3 -m unittest discover -s python/tests -p test_divisor_sum.py -v
