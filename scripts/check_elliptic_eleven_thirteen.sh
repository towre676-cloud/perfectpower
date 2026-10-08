#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONPATH=python
python3 -m unittest discover -s python/tests -p test_elliptic_eleven_thirteen.py -v
python3 -m unittest discover -s python/tests -p test_mordell_cover_charts.py -v
python3 python/develop_elliptic_eleven_thirteen.py
