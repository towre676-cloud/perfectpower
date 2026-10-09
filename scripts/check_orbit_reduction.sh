#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build PerfectPower.AutomaticReduction PerfectPower.MordellParity
lake env lean audit/OrbitReduction.lean
lake env python3 -m unittest discover -s python/tests -p 'test_orbit_reduction_push.py'
