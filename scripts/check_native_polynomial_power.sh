#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
bash scripts/check_native_power.sh
lake env lean PerfectPower/NativePolynomialSquare.lean -o .lake/build/lib/lean/PerfectPower/NativePolynomialSquare.olean
lake env lean PerfectPower/FastDivisors.lean -o .lake/build/lib/lean/PerfectPower/FastDivisors.olean
lake env lean PerfectPower/NativePolynomialRoots.lean -o .lake/build/lib/lean/PerfectPower/NativePolynomialRoots.olean
lake env lean PerfectPower/NativeDivisorSquare.lean -o .lake/build/lib/lean/PerfectPower/NativeDivisorSquare.olean
lake env lean PerfectPower/Tactic/NativePolynomialPower.lean -o .lake/build/lib/lean/PerfectPower/Tactic/NativePolynomialPower.olean
lake env lean -s 65536 audit/NativePolynomialPower.lean
