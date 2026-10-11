#!/usr/bin/env python3
"""Audit post-selection ablation scopes, generated sources and original logs."""
import argparse
import hashlib
import json
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from ablate_model_counting import variants
from check_model_counting_receipts import exact_from_log,require


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('receipt',type=Path);p.add_argument('--screen',type=Path,required=True)
    p.add_argument('--previous-root',type=Path,required=True);p.add_argument('--work-directory',type=Path)
    a=p.parse_args();d=json.loads(a.receipt.read_text());screen=json.loads(a.screen.read_text())
    require(d['schema']=='pp-cnf-ablation/1' and d['completed'],'incomplete ablation')
    require(d['screen_sha256']==sha(a.screen),'selection screen changed')
    current=(ROOT/'native/model_counting/counter.cpp').read_text()
    prior=(a.previous_root/'native/model_counting/counter.cpp').read_text()
    require(d['native_source_sha256']==hashlib.sha256(current.encode()).hexdigest(),'native source changed')
    require(d['previous_source_sha256']==hashlib.sha256(prior.encode()).hexdigest(),'prior native source changed')
    source=variants(current,prior)
    require(d['variant_source_sha256']=={k:hashlib.sha256(v.encode()).hexdigest() for k,v in source.items()},'variant recipe differs')
    require(set(d['variant_binary_sha256'])==set(source),'variant binary scope differs')
    for key,path in [('python','python/perfectpower/model_counting.py'),('execution','python/run_model_counting.py'),('ablation_runner','python/ablate_model_counting.py')]:
        require(d['source_identities'][key]==sha(ROOT/path),'ablation source changed')
    expected={r['name']:r['solvers']['perfectpower']['count'] for r in screen['results'] if r['solvers']['perfectpower']['status']=='EXACT'}
    names=d['instances'];require(len(names)==len(set(names)) and set(names)<=set(expected),'invalid selection')
    require([(r['trial'],r['name']) for r in d['results']]==[(t,n) for t in range(d['repetitions']) for n in names],'incomplete trial scope')
    total=0
    if a.work_directory:
        for name,text in source.items():require((a.work_directory/name/'native/model_counting/counter.cpp').read_text()==text,'saved variant differs')
    for r in d['results']:
        require(set(r['variants'])==set(source),'variant outcome scope differs')
        for outcome in r['variants'].values():
            require('command' not in outcome and Path(outcome['log']).name==outcome['log'],'nonportable outcome')
            require(outcome['seconds']>=0,'negative elapsed time')
            if a.work_directory:
                log=a.work_directory/'logs'/outcome['log'];require(sha(log)==outcome['log_sha256'],'ablation log changed')
            if outcome['status']=='EXACT':
                require(outcome['exit_code']==0 and outcome['count']==expected[r['name']],'ablation count differs')
                if a.work_directory:require(exact_from_log(log)==outcome['count'],'ablation log/count differs')
            else:require(outcome['count'] is None,'failed outcome carries count')
            total+=1
    print(json.dumps({'status':'PASS','instances':len(names),'outcomes':total,'logs_verified':a.work_directory is not None}))


if __name__=='__main__':main()
