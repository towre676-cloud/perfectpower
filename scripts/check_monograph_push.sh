#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 python/build_monograph_lean.py
mkdir -p .lake/build/lib/lean/PerfectPower/Generated
for module in NativeNearSquare NativePolynomialSquare FastDivisors NativePolynomialRoots NativePowerRoots LinearPerturbation RungePolynomial RungePower; do
  lake env lean -s65536 "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
while IFS= read -r module; do
  lake env lean -s65536 "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done < <(python3 -c 'import json; print("\n".join(json.load(open("receipts/monograph_lean/inputs.json"))["modules"]))')
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean -s65536 audit/MonographPush.lean > "$log"
python3 python/audit_monograph_lean.py "$log"
