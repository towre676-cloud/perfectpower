"""Independent bounded #SAT baseline using a uniquely extendible adder CNF."""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
from time import perf_counter
from perfectpower.planning_cnf import encode_allocation
from perfectpower.model_counting import CNFCounter
from perfectpower.planning import CompletionPlanner
from run_planning import parse_public
from run_planning_population import OUT, save

def run(args):
    spec = next(r['specification'] for r in parse_public() if len(r['specification']['variables']) == args.case)
    prefix = [int(c) for c in args.prefix]
    assert len(prefix) <= args.case
    t = perf_counter()
    formula, circuit = encode_allocation(spec)
    assumptions = [j+1 if bit else -j-1 for j, bit in enumerate(prefix)]
    dimacs = formula.dimacs(assumptions)
    path = OUT/f'{args.case}_adder_{args.prefix or "root"}.cnf'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(dimacs)
    r = {'schema': 'pp-planning-cnf-baseline/1', 'case': args.case, 'prefix': prefix,
         'solver': 'ganak' if args.ganak else 'perfectpower_cnf',
         'encoding': 'functional ripple adders and comparators; unprojected unique extensions',
         'original_variables': args.case, 'cnf_variables': formula.variables,
         'clauses': len(formula.clauses)+len(prefix), 'cnf_sha256': hashlib.sha256(dimacs.encode()).hexdigest(),
         'encoding_seconds': perf_counter()-t, 'time_limit_seconds': args.timeout,
         'counting_scope': 'complete feasible population under original prefix; no objective optimization'}
    t = perf_counter()
    if args.ganak:
        command = [str(args.ganak.resolve()), '--prob', '0', '--verb', '0', '--maxcache', '128', str(path.resolve())]
        logpath = path.with_suffix('.ganak.log')
        def cap():
            resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
        with logpath.open('w') as log:
            try:
                p = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout, preexec_fn=cap)
                r['returncode'] = p.returncode
                answers = [line.split()[-1] for line in logpath.read_text().splitlines() if line.startswith(('s exact arb int ', 'c s exact arb int '))]
                if p.returncode == 0 and len(answers) == 1:
                    r.update(status='complete', count=int(answers[0]))
                else:
                    r['status'] = 'solver_error'
            except subprocess.TimeoutExpired:
                r['status'] = 'TIME_LIMIT'
        r['binary_sha256'] = hashlib.sha256(args.ganak.read_bytes()).hexdigest()
        r['command'] = command[:-1]+[path.name]
        r['peak_rss_bytes'] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss*1024
        r['address_space_limit_bytes'] = 1024**3
    else:
        with CNFCounter(formula, cache_bytes=128*1024**2, timeout=args.timeout) as counter:
            r['answer'] = counter.result(assumptions)
            r['status'] = r['answer']['status']
            if r['status'] == 'EXACT':
                r['count'] = int(r['answer']['count'])
        r['peak_rss_bytes'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024
    r['counting_seconds'] = perf_counter()-t
    if 'count' in r and args.case <= 20:
        p = CompletionPlanner(dict(spec, strategy='gray'))
        assert p.completions(prefix)['count'] == r['count']
        r['independent_gray_agreement'] = True
    save(OUT/f'{args.case}_{r["solver"]}_{args.prefix or "root"}.json', r)
    print(json.dumps(r), flush=True)

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--case', type=int, required=True)
    ap.add_argument('--prefix', default='')
    ap.add_argument('--ganak', type=Path)
    ap.add_argument('--timeout', type=float, default=60)
    args = ap.parse_args()
    if any(c not in '01' for c in args.prefix) or not 0 < args.timeout <= 3600:
        ap.error('binary prefix and timeout in (0,3600] required')
    run(args)
