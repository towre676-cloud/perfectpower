#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONPATH=python
python3 -m unittest discover -s python/tests -p test_torsion_index_pell7.py -v
python3 python/develop_torsion_index_pell7.py
python3 python/crosscheck_torsion_index_pell7.py
