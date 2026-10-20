#!/usr/bin/env python3
"""Recompute the source-bound exact trace-form and normalizer certificate."""
import hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from perfectpower.coxeter_normalizer import receipt
if __name__=='__main__':
    r=receipt()
    paths=['python/perfectpower/coxeter_normalizer.py','python/perfectpower/e8_periods.py',
           'python/perfectpower/exact_linear.py','python/tests/test_coxeter_normalizer.py',
           'docs/COXETER_TRACE_NORMALIZER.md','scripts/verify_coxeter_normalizer.py']
    r['source_sha256']={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in paths}
    target=ROOT/'receipts/period_bridge_deep/trace_normalizer.json'
    target.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'normalizer_order':r['normalizer_order'],'centralizer_order':r['centralizer_order'],'nonsplit':True}))
