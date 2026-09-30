#!/usr/bin/env python3
"""Run an installed SMT solver without shell execution or automatic harness flags."""
import argparse
import datetime
import json
import pathlib
import shutil
import subprocess
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--solver', required=True, help='executable name or absolute path')
    p.add_argument('--solver-arg', action='append', default=[], help='repeat; use --solver-arg=--incremental')
    p.add_argument('--cohort', choices=['elster','cvc5','staub','all'], default='cvc5')
    p.add_argument('--timeout', type=float, default=2.0, help='seconds per entire source file, not per query')
    p.add_argument('--limit', type=int, default=0, help='0 means all selected files')
    p.add_argument('--output', type=pathlib.Path, default=ROOT/'reports/baseline.json')
    a = p.parse_args()
    solver = shutil.which(a.solver)
    if not solver:
        p.error('solver executable not found; install z3 or cvc5 first')
    if a.timeout <= 0 or a.limit < 0:
        p.error('timeout must be positive and limit nonnegative')
    inventory_path = ROOT/'reports/structural_inventory.json'
    if not inventory_path.exists():
        p.error('run tools/inspect_corpus.py first')
    rows = json.loads(inventory_path.read_text())
    repo = {'elster':'SMT-LIB/benchmark-submission','cvc5':'cvc5/cvc5','staub':'mikekben/STAUB'}
    rows = sorted((r for r in rows if 'error' not in r and (a.cohort=='all' or r['repository']==repo[a.cohort])),key=lambda r:r['local_path'])
    if a.limit:
        rows = rows[:a.limit]
    try:
        version = subprocess.run([solver,'--version'],capture_output=True,text=True,timeout=5)
        version_text = (version.stdout+version.stderr)[:2000]
    except (OSError,subprocess.TimeoutExpired) as e:
        version_text = str(e)
    output = []
    for row in rows:
        command = [solver,*a.solver_arg,str(ROOT/row['local_path'])]
        started = time.perf_counter()
        try:
            run = subprocess.run(command,capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=a.timeout)
            stdout, stderr = run.stdout, run.stderr
            result = {'outcome':'finished','returncode':run.returncode}
        except subprocess.TimeoutExpired as e:
            decode = lambda v: v.decode('utf-8','replace') if isinstance(v,bytes) else (v or '')
            stdout,stderr = decode(e.stdout),decode(e.stderr)
            result = {'outcome':'timeout','returncode':None}
        elapsed = time.perf_counter()-started
        statuses = [s.strip() for s in stdout.splitlines() if s.strip() in ('sat','unsat','unknown')]
        nchecks = len(row['check_sat_queries'])
        result.update({'local_path':row['local_path'],'command':command,'wall_seconds':elapsed,
                       'query_count':nchecks,'statuses':statuses,
                       'fully_answered':result['outcome']=='finished' and result['returncode']==0 and len(statuses)==nchecks and '(error' not in stdout,
                       'original_harness_command_lines':row['harness_command_lines'],
                       'original_harness_directives':row['harness_directives'],
                       'expected_harness_failure':row['expected_harness_failure'],
                       'harness_flags_applied':False,'original_harness_expectations':row['harness_expectations'],
                       'status_annotations':[x['last_status_annotation'] for x in row['check_sat_queries']],
                       'stdout_prefix':stdout[:8000],'stderr_prefix':stderr[:8000]})
        output.append(result)
        print(row['local_path'], result['outcome'], f'{elapsed:.3f}s', f'{len(statuses)}/{nchecks} statuses',flush=True)
    report = {'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'solver':solver,'solver_version':version_text,'solver_arguments':a.solver_arg,
              'timeout_seconds_per_file':a.timeout,'cohort':a.cohort,'results':output,
              'method':'No source rewrite; no automatic execution of harness comments. Per-file times include startup. Statuses are solver claims, not checked certificates.'}
    a.output.parent.mkdir(parents=True,exist_ok=True)
    a.output.write_text(json.dumps(report,indent=2)+'\n')

if __name__ == '__main__':
    main()
