#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower/Tactic
lake env lean PerfectPower/NativeNearSquare.lean -o .lake/build/lib/lean/PerfectPower/NativeNearSquare.olean
lake env lean PerfectPower/FunctionFieldPower.lean -o .lake/build/lib/lean/PerfectPower/FunctionFieldPower.olean
lake env lean PerfectPower/Tactic/NativePower.lean -o .lake/build/lib/lean/PerfectPower/Tactic/NativePower.olean
lake env lean audit/NativePower.lean
