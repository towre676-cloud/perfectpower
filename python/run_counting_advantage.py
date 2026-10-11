#!/usr/bin/env python3
"""Run frozen selected cohorts serially, including all predicted repeat failures."""
import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT=Path(__file__).resolve().parent.parent


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--evidence',type=Path,required=True)
    p.add_argument('--previous-root',type=Path,required=True)
    p.add_argument('--ganak',type=Path,required=True)
    p.add_argument('--d4',type=Path,required=True)
    a=p.parse_args();directory=ROOT/'receipts/model_counting'
    files=[ROOT/'native/model_counting/counter.cpp',Path(__file__),ROOT/'docs/MODEL_COUNTING_ADVANTAGE_PROTOCOL.md',ROOT/'docs/MODEL_COUNTING_DYNASP_PROTOCOL.md']
    files+=[directory/f'advantage_{label}_selection.json'for label in ('fresh','dynasp')]
    frozen={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest()for f in files}
    identity=directory/'advantage_run_protocol.json'
    if identity.exists():raise ValueError('fresh run required')
    identity.write_text(json.dumps({'schema':'pp-cnf-advantage-run/1','frozen_sources':frozen,
                                   'native_baseline':'0.10.1 d4dc8dc6fa5ba5f6c6f11e81ccd766e1d3bdf3cc',
                                   'timeout_seconds':5,'memory_gib':6},indent=2)+'\n')
    def execute(script,args):
        assert all(hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h for n,h in frozen.items())
        subprocess.run([sys.executable,str(ROOT/'python'/script),*map(str,args)],cwd=ROOT,check=True)
    def compare(label,suffix,selection,names=None,repetitions=1,timeout=5):
        output=directory/f'advantage_{label}_{suffix}.json'
        if output.exists():
            d=json.loads(output.read_text());assert d['completed']
        else:
            args=['--manifest',ROOT/f'data/model_counting/advantage_{label}_manifest.json',
                  '--corpus',a.evidence/label,'--previous-root',a.previous_root,'--ganak',a.ganak,'--d4',a.d4,
                  '--timeout',timeout,'--memory-gib',6,'--repetitions',repetitions,
                  '--output',output,'--log-directory',a.evidence/f'{label}_{suffix}']
            if names:args+=['--names',*names]
            execute('compare_model_counting.py',args);d=json.loads(output.read_text())
        execute('analyze_counting_structure.py',['--selection',selection,'--receipt',output,'--output',directory/f'advantage_{label}_{suffix}_analysis.json'])
        for row in d['results']:
            assert len({s['count']for s in row['solvers'].values()if s['status']=='EXACT'})<=1
        return d
    for label in ('fresh','dynasp'):
        selection=directory/f'advantage_{label}_selection.json';data=json.loads(selection.read_text())
        names=sorted(r['name']for r in data['selected']if r['status']=='PREDICTED_TRACTABLE')
        screen=compare(label,'screen',selection)
        repeated=compare(label,'repeated',selection,names=names,repetitions=3)
        current={r['name']for d in (screen,repeated)for r in d['results']if r['solvers']['perfectpower']['status']=='EXACT'}
        confirmed={r['name']for d in (screen,repeated)for r in d['results']if any(r['solvers'][s]['status']=='EXACT'for s in ('ganak','d4_2024'))}
        if current-confirmed:compare(label,'confirmation',selection,names=sorted(current-confirmed),timeout=30)
    execute('audit_counting_advantage.py',['--evidence',a.evidence,'--previous-root',a.previous_root,'--output',directory/'advantage_validation.json'])


if __name__=='__main__':main()
