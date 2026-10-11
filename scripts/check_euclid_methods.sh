#!/usr/bin/env bash
set -euo pipefail
lean_bin="${PERFECTPOWER_LEAN:-lean}"
euclid_tmp=$(mktemp -d)
trap 'rm -rf "$euclid_tmp"' EXIT
mkdir -p "$euclid_tmp/PerfectPower"
"$lean_bin" -o "$euclid_tmp/PerfectPower/EuclidMethods.olean" PerfectPower/EuclidMethods.lean
export LEAN_PATH="$euclid_tmp${LEAN_PATH:+:$LEAN_PATH}"
"$lean_bin" receipts/euclid_methods/SourceBoundBezout.lean
"$lean_bin" receipts/euclid_methods/HigherDegreeBezout.lean
"$lean_bin" receipts/euclid_methods/SourceBoundSqrt.lean
