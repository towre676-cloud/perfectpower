#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONPATH=python
python -m unittest discover -s python/tests -p test_positive_geometry.py -v
python python/build_positive_geometry.py
