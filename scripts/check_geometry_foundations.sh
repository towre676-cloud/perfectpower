#!/usr/bin/env bash
set -euo pipefail
lean_bin="${PERFECTPOWER_LEAN:-lean}"
geometry_tmp=$(mktemp -d)
trap 'rm -rf "$geometry_tmp"' EXIT
mkdir -p "$geometry_tmp/PerfectPower"
"$lean_bin" -o "$geometry_tmp/PerfectPower/GeometryFoundations.olean" PerfectPower/GeometryFoundations.lean
export LEAN_PATH="$geometry_tmp${LEAN_PATH:+:$LEAN_PATH}"
for name in Rotation Reflection TriangleAreas; do
  "$lean_bin" "receipts/belyaev_geometry/$name.lean"
done
python3 scripts/check_geometry_rejections.py > receipts/belyaev_geometry/kernel-rejection.log
python3 scripts/record_geometry_validation.py
