#!/usr/bin/env bash
set -euo pipefail
export PYTHONPATH="${PYTHONPATH:+$PYTHONPATH:}python"
export PERFECTPOWER_LEAN="${PERFECTPOWER_LEAN:-lean}"
lake env python3 python/develop_soe_generic.py
lake env python3 -m unittest discover -s python/tests -p 'test_checked_soe.py' -v
lake env python3 -m unittest discover -s python/tests -p 'test_soe_bridge.py' -v
lake build PerfectPower.SOESemantics
python3 python/develop_new_work_lean.py
lake env lean -s 65536 PerfectPower/Generated/SOEGenericPackets.lean
lake env lean -s 65536 PerfectPower/Generated/SOEModelPackets.lean
