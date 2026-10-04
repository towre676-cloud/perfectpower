#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
bash scripts/check_native_polynomial_power.sh
lake env lean PerfectPower/LocalQuarticObstruction.lean -o .lake/build/lib/lean/PerfectPower/LocalQuarticObstruction.olean
lake env lean audit/LocalQuarticObstruction.lean
PYTHONPATH=python python3 -m unittest python.tests.test_divisor_reuse
