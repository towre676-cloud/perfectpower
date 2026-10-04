#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 python/build_root_event_lean.py
python3 python/build_graph_probability_lean.py
python3 python/audit_root_events_lean.py --manifest
mkdir -p .lake/build/lib/lean/PerfectPower/Generated
for module in NativeNearSquare NativePolynomialSquare; do
  lake env lean -s65536 "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done
while IFS= read -r module; do
  lake env lean -s65536 "PerfectPower/$module.lean" -o ".lake/build/lib/lean/PerfectPower/$module.olean"
done < <(python3 -c 'import json; print("\n".join(json.load(open("receipts/root_events_lean/inputs.json"))["modules"]))')
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean -s65536 audit/RootEvents.lean > "$log"
python3 python/audit_root_events_lean.py "$log"
