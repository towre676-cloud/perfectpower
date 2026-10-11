#!/usr/bin/env python3
"""Verify complete paired receipts, frozen sources and optional separate logs."""
import argparse
import hashlib
import json
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from compare_model_counting import summarize
from check_model_counting_receipts import exact_from_log,require


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(receipt_path,manifest_path,logs=None,previous=None):
    receipt=json.loads(receipt_path.read_text());manifest=json.loads(manifest_path.read_text())
    require(receipt['schema']=='pp-cnf-paired/1' and receipt['completed'],'incomplete/unknown receipt')
    require(receipt['source_identities']['manifest']==sha(manifest_path),'manifest changed')
    lookup={r['name']:r for r in manifest['instances']}
    names=receipt['instances'];solvers=receipt['solver_scope'];repeats=receipt['repetitions']
    require(len(set(names))==len(names) and set(names)<=set(lookup),'invalid scope')
    require([(r['trial'],r['name']) for r in receipt['results']]==[(t,n) for t in range(repeats) for n in names],'missing, duplicated or reordered results')
    for key,path in [('counter','native/model_counting/counter.cpp'),('python','python/perfectpower/model_counting.py'),('runner','python/compare_model_counting.py'),('execution','python/run_model_counting.py')]:
        require(receipt['source_identities'][key]==sha(ROOT/path),'current source changed: '+key)
    if previous:
        for key,path in [('previous_counter','native/model_counting/counter.cpp'),('previous_python','python/perfectpower/model_counting.py'),('previous_worker','python/run_model_counting.py')]:
            require(receipt['source_identities'][key]==sha(previous/path),'prior source changed: '+key)
    references=json.loads((ROOT/'data/model_counting/references.json').read_text())
    for name,key in [('ganak','ganak_binary'),('d4_2024','d4_binary')]:
        if name in solvers:require(receipt['source_identities'][key]==references['ganak' if name=='ganak' else 'd4']['binary_sha256'],'reference changed')
    total=0
    for row in receipt['results']:
        require(row['sha256']==lookup[row['name']]['sha256'],'instance changed')
        require(set(row['solvers'])==set(solvers),'solver scope changed')
        exact=[]
        for solver,outcome in row['solvers'].items():
            require('command' not in outcome,'receipt contains environment command')
            require(outcome['seconds']>=0,'negative elapsed time')
            require(Path(outcome['log']).name==outcome['log'],'nonportable log name')
            if logs:
                path=logs/outcome['log'];require(sha(path)==outcome['log_sha256'],'log differs')
            if outcome['status']=='EXACT':
                count=outcome['count'];require(isinstance(count,str) and count.isascii() and count.isdigit() and outcome['exit_code']==0,'invalid exact count')
                if logs:require(exact_from_log(path)==count,'log/count differs')
                exact.append(count)
            else:require(outcome['count'] is None,'nonexact answer carries count')
            total+=1
        require(len(set(exact))<=1,'count disagreement')
        require(row['agreement']==('MATCH' if len(exact)>1 else 'UNCONFIRMED'),'agreement differs')
    require(receipt['summary']==summarize(receipt['results'],solvers,receipt['timeout_seconds']),'summary differs')
    print(json.dumps({'receipt':receipt_path.name,'instances':len(names),'repetitions':repeats,'outcomes':total,'logs_verified':logs is not None,'status':'PASS'}))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('receipt',type=Path);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--logs',type=Path);p.add_argument('--previous-root',type=Path)
    a=p.parse_args();check(a.receipt,a.manifest,a.logs,a.previous_root)
