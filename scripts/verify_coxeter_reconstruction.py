#!/usr/bin/env python3
"""Recompute exact positive folded and oriented Coxeter spectral certificates."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'python'))
from perfectpower.coxeter_reconstruction import receipt

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=ROOT/'receipts/period_bridge_deep/coxeter_reconstruction.json')
    args = parser.parse_args()
    result = receipt()
    paths = ['python/perfectpower/coxeter_reconstruction.py', 'python/perfectpower/raghava_coxeter.py',
             'python/perfectpower/period_transport.py', 'python/perfectpower/e8_periods.py',
             'python/tests/test_coxeter_reconstruction.py', 'scripts/verify_coxeter_reconstruction.py',
             'docs/COXETER_RECONSTRUCTION.md']
    result['source_sha256'] = {p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'output': str(args.output), 'reflection_even_coordinates': 9, 'reflection_odd_coordinates': 4,
                      'adjoint_even_coordinates': 33, 'adjoint_odd_coordinates': 14}))
