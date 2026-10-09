#!/usr/bin/env bash
set -euo pipefail
lake build PerfectPower.MordellDescentMask
log=$(mktemp)
trap 'rm -f "$log"' EXIT
mkdir -p .lake/build/lib/lean/PerfectPower/MordellDescentAtlas
for file in PerfectPower/MordellDescentAtlas/Block*.lean; do
  lake env lean -j 2 "$file" -o ".lake/build/lib/lean/${file%.lean}.olean" >> "$log" 2>&1
done
python3 python/record_mordell_descent_atlas.py "$log"
