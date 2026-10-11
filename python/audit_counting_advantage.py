#!/usr/bin/env python3
"""Check complete selected scopes, frozen identities and retained query logs."""
import argparse
import hashlib
import json
from pathlib import Path
from audit_structural_study import exact_from_log

ROOT=Path(__file__).resolve().parent.parent


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--evidence',type=Path,required=True)
    p.add_argument('--previous-root',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();receipts=ROOT/'receipts/model_counting'
    reference=json.loads((ROOT/'data/model_counting/references.json').read_text())
    counter=sha(ROOT/'native/model_counting/counter.cpp')
    reports=[];answers={};current={};refs={};logs=0
    for label in ('fresh','dynasp'):
        selection=json.loads((receipts/f'advantage_{label}_selection.json').read_text())
        manifest_path=ROOT/f'data/model_counting/advantage_{label}_manifest.json'
        manifest=json.loads(manifest_path.read_text());instances={r['name']:r for r in manifest['instances']}
        assert selection['completed']and selection['counter_sha256']==counter
        assert selection['manifest_sha256']==sha(manifest_path)
        assert {r['name']for r in selection['selected']}==set(instances)
        predicted={r['name']for r in selection['selected']if r['status']=='PREDICTED_TRACTABLE'}
        for suffix in ('screen','repeated','confirmation'):
            file=receipts/f'advantage_{label}_{suffix}.json'
            if suffix=='confirmation'and not file.exists():continue
            d=json.loads(file.read_text());assert d['completed']
            if suffix=='screen':assert set(d['instances'])==set(instances)
            if suffix=='repeated':assert set(d['instances'])==predicted and d['repetitions']==3
            assert d['source_identities']['counter']==counter
            assert d['source_identities']['manifest']==sha(manifest_path)
            checks={'python':ROOT/'python/perfectpower/model_counting.py','runner':ROOT/'python/compare_model_counting.py',
                    'execution':ROOT/'python/run_model_counting.py','previous_counter':a.previous_root/'native/model_counting/counter.cpp',
                    'previous_python':a.previous_root/'python/perfectpower/model_counting.py','previous_worker':a.previous_root/'python/run_model_counting.py'}
            for key,path in checks.items():assert d['source_identities'][key]==sha(path)
            for key,solver in [('ganak_binary','ganak'),('d4_binary','d4')]:
                assert d['source_identities'][key]==reference[solver]['binary_sha256']
            expected={(n,t)for n in d['instances']for t in range(d['repetitions'])}
            assert len(d['results'])==len(expected)
            assert {(r['name'],r['trial'])for r in d['results']}==expected
            for row in d['results']:
                assert row['sha256']==instances[row['name']]['sha256']
                assert set(row['solvers'])==set(d['solver_scope'])
                for solver,v in row['solvers'].items():
                    assert Path(v['log']).name==v['log']
                    path=a.evidence/f'{label}_{suffix}'/v['log'];assert sha(path)==v['log_sha256'];logs+=1
                    if v['status']=='EXACT':
                        assert exact_from_log(path)==v['count']
                        answers.setdefault(row['sha256'],set()).add(v['count'])
                        if solver=='perfectpower':current[row['sha256']]=v['count']
                        if solver not in ('perfectpower','previous'):refs.setdefault(row['sha256'],set()).add(v['count'])
            reports.append({'receipt':file.name,'sha256':sha(file),'queries':len(d['results'])})
    assert all(len(values)==1 for values in answers.values())
    confirmed=[key for key,value in current.items()if value in refs.get(key,set())]
    report={'schema':'pp-cnf-advantage-audit/1','source_sha256':sha(Path(__file__)),
            'counter_sha256':counter,'receipts':reports,'raw_logs_verified':logs,
            'current_exact_inputs':len(current),'independently_confirmed_inputs':len(confirmed),
            'unconfirmed_input_hashes':sorted(set(current)-set(confirmed)),'count_disagreements':0}
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))


if __name__=='__main__':main()
