#!/usr/bin/env python3
"""Refresh shared exact-browser source identities without changing product data."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def export():
    p=ROOT/'web/shared/finite-counter.js';raw=p.read_text()
    result={'schema':'pp-browser-counter/1','api':'PerfectPowerCounter','source_path':p.relative_to(ROOT).as_posix(),'source':raw,'sha256':hashlib.sha256(raw.encode()).hexdigest(),
            'scope':'Finite integer factor counts; probabilities depend on the supplied model, not a claim of sports-prediction advantage.'}
    (ROOT/'data/browser_counter.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    registry=json.loads((ROOT/'data/app_ecosystem.json').read_text())
    if len({p['id'] for p in registry['products']})!=4:raise ValueError('Exactly four distinct product identities required')
    for p in registry['products']:
        if not set(p['sources'])<=set(registry['upstreams']):raise ValueError('Unknown upstream dependency')
        if not p['site'].startswith('https://') or not p['open'].startswith('https://'):raise ValueError('Published HTTPS product routes required')
    return {'products':len(registry['products']),'counter_sha256':result['sha256']}
if __name__=='__main__':print(json.dumps(export()))
