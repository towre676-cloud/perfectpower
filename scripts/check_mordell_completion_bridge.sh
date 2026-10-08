#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean/PerfectPower receipts/mordell_formal_completion
lake env lean PerfectPower/MordellCompletionBridge.lean \
  -o .lake/build/lib/lean/PerfectPower/MordellCompletionBridge.olean \
  > receipts/mordell_formal_completion/build.log 2>&1
lake env lean audit/MordellCompletionBridge.lean \
  > receipts/mordell_formal_completion/axioms.log 2>&1
python3 python/reconcile_mordell_formal_completion.py
