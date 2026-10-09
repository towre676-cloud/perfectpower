#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower/MordellParityAtlas
lake build PerfectPower.MordellParity
log_file="$(mktemp)"
trap 'rm -f "$log_file"' EXIT
for source in PerfectPower/MordellParityAtlas/Block*.lean; do
  lake env lean -j2 "$source" -o ".lake/build/lib/lean/${source%.lean}.olean" >> "$log_file" 2>&1
done
python3 python/record_mordell_parity.py "$log_file"
PYTHONPATH=python python3 -m unittest discover -s python/tests -p 'test_mordell_parity.py'
