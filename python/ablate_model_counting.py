#!/usr/bin/env python3
"""Descriptive, post-selection, single-feature ablations of the exact counter."""
import argparse
import hashlib
import json
import sys
from pathlib import Path
import perfectpower.model_counting as counting
from run_model_counting import ROOT, acquire_output_lock, run


def variants(current, previous):
    quotient='unsigned removed=quotient(f,active,contradiction);'
    if current.count(quotient)!=1:raise ValueError('quotient marker changed')
    start=current.index('  // A filled primal graph')
    end=current.index('  struct Factor',start)
    old_start=previous.index('  std::vector<std::vector<int>> scopes;')
    old_end=previous.index('  struct Factor',old_start)
    unit_start=current.index('  check(depth);')
    unit_end=current.index('  unsigned active=dense',unit_start)
    old_unit_start=previous.index('  check(depth);')
    old_unit_end=previous.index('  unsigned active=dense',old_unit_start)
    dense_start=current.index(' static unsigned dense(')
    dense_end=current.index(' static std::string key(',dense_start)
    old_dense_start=previous.index(' static unsigned dense(')
    old_dense_end=previous.index(' static std::string key(',old_dense_start)
    return {
        'full':current,
        'without_equivalence':current.replace(quotient,'unsigned removed=0;'),
        'without_graph_planner':current[:start]+previous[old_start:old_end]+current[end:],
        'without_occurrence_queue':current[:unit_start]+previous[old_unit_start:old_unit_end]+current[unit_end:],
        'without_direct_dense_map':current[:dense_start]+previous[old_dense_start:old_dense_end]+current[dense_end:],
    }


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--worker',type=Path);p.add_argument('--variant-root',type=Path)
    p.add_argument('--previous-root',type=Path);p.add_argument('--screen',type=Path)
    p.add_argument('--corpus',type=Path);p.add_argument('--names',nargs='+')
    p.add_argument('--output',type=Path);p.add_argument('--work-directory',type=Path)
    p.add_argument('--timeout',type=float,default=10);p.add_argument('--repetitions',type=int,default=3)
    a=p.parse_args()
    if a.worker:
        counting.runtime_root=lambda:a.variant_root
        from run_model_counting import worker
        return worker(a.worker,a.timeout)
    if not all([a.previous_root,a.screen,a.corpus,a.names,a.output,a.work_directory]):p.error('all experiment paths and explicit names required')
    if not 0<a.timeout<=120 or not 1<=a.repetitions<=10:p.error('bounded experiment required')
    with acquire_output_lock(ROOT/'receipts/model_counting/comparison-serial'):
        if a.output.exists():raise RuntimeError('refusing to overwrite ablation')
        screen=json.loads(a.screen.read_text())
        if not screen['completed']:raise ValueError('completed selection screen required')
        expected={r['name']:r['solvers']['perfectpower']['count'] for r in screen['results'] if r['solvers']['perfectpower']['status']=='EXACT'}
        hashes={r['name']:r['sha256'] for r in screen['results']}
        if len(set(a.names))!=len(a.names) or set(a.names)-set(expected):raise ValueError('ablation scope must be explicitly solved screen cases')
        current=(ROOT/'native/model_counting/counter.cpp').read_text()
        prior=(a.previous_root/'native/model_counting/counter.cpp').read_text()
        if hashlib.sha256(current.encode()).hexdigest()!=screen['source_identities']['counter']:
            raise ValueError('counter differs from completed selection screen')
        sources=variants(current,prior);roots={};binaries={};binary_paths={}
        frozen_paths={'python':ROOT/'python/perfectpower/model_counting.py',
                      'execution':ROOT/'python/run_model_counting.py',
                      'ablation_runner':Path(__file__).resolve()}
        frozen={k:hashlib.sha256(v.read_bytes()).hexdigest() for k,v in frozen_paths.items()}
        for name,source in sources.items():
            root=a.work_directory/name;path=root/'native/model_counting/counter.cpp';path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(source);roots[name]=root.resolve()
            counting.runtime_root=lambda root=root:root
            counting._library=None;library=counting.native_library()
            binaries[name]=hashlib.sha256(Path(library._name).read_bytes()).hexdigest()
            binary_paths[name]=Path(library._name)
        report={'schema':'pp-cnf-ablation/1','selection':'Descriptive post-selection mechanism test, not an independent performance holdout',
                'screen_sha256':hashlib.sha256(a.screen.read_bytes()).hexdigest(),
                'native_source_sha256':hashlib.sha256(current.encode()).hexdigest(),
                'previous_source_sha256':hashlib.sha256(prior.encode()).hexdigest(),
                'variant_source_sha256':{k:hashlib.sha256(v.encode()).hexdigest() for k,v in sources.items()},
                'variant_binary_sha256':binaries,
                'source_identities':frozen,
                'instances':a.names,'timeout_seconds':a.timeout,'memory_gib':6,'repetitions':a.repetitions,
                'timing_scope':'Serial cold Python subprocess wall time including input parsing, construction and query; variant compilation warmed separately',
                'results':[],'completed':False}
        logs=a.work_directory/'logs';logs.mkdir(parents=True,exist_ok=True)
        def save():a.output.write_text(json.dumps(report,indent=2)+'\n')
        save()
        for trial in range(a.repetitions):
            for name in a.names:
                path=a.corpus/name
                if hashlib.sha256(path.read_bytes()).hexdigest()!=hashes[name]:raise ValueError('input changed')
                if (ROOT/'native/model_counting/counter.cpp').read_text()!=current:raise ValueError('counter changed')
                if any(hashlib.sha256(v.read_bytes()).hexdigest()!=frozen[k] for k,v in frozen_paths.items()):
                    raise ValueError('frozen ablation source changed')
                row={'name':name,'trial':trial,'variants':{}}
                order=list(sources);rotation=(trial+a.names.index(name))%len(order);order=order[rotation:]+order[:rotation]
                for variant in order:
                    if (roots[variant]/'native/model_counting/counter.cpp').read_text()!=sources[variant]:
                        raise ValueError('variant source changed')
                    if hashlib.sha256(binary_paths[variant].read_bytes()).hexdigest()!=binaries[variant]:
                        raise ValueError('variant binary changed')
                    log=logs/f'{name}.{trial}.{variant}.log'
                    command=[sys.executable,str(Path(__file__).resolve()),'--worker',str(path),
                             '--variant-root',str(roots[variant]),'--timeout',str(a.timeout)]
                    answer=run(command,a.timeout,6*1024**3,log);answer.pop('command',None);answer['log']=log.name
                    answer['log_sha256']=hashlib.sha256(log.read_bytes()).hexdigest()
                    if answer['status']=='EXACT' and answer['count']!=expected[name]:raise RuntimeError('ablation count mismatch')
                    row['variants'][variant]=answer
                report['results'].append(row);save()
                print(name,trial,{k:(v['status'],round(v['seconds'],3)) for k,v in row['variants'].items()},flush=True)
        report['completed']=True;save()


if __name__=='__main__':main()
