"""Rebuild the divisor-sum atlas using only the Python standard library."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path
from perfectpower.divisor_sum import (sigma_sieve, exact_root, prime_power_rows,
                                     prime_pair_squares)
from perfectpower.linear_perturbation import solve, solve_square_leading


def build(output, limit=1_000_000, prime_limit=1000, max_exponent=8):
    out=Path(output); out.mkdir(parents=True,exist_ok=True)
    files={}
    def write(name,value):
        path=out/name
        path.write_text(json.dumps(value,separators=(',',':'),sort_keys=True)+'\n')
        files[name]={'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
    sigma, primes=sigma_sieve(limit)
    hits={str(d):[] for d in range(2,9)}
    for n in range(1,limit+1):
        for d in range(2,9):
            root=exact_root(sigma[n],d)
            if root is not None:
                hits[str(d)].append([n,sigma[n],root])
    write('bounded_power_hits.json',{'schema':'pp-sigma-bounded/1','domain':[1,limit],
          'degrees':list(range(2,9)),'complete_in_domain':True,'globally_complete':False,
          'execution_verified':False,'hits':hits})
    rows=prime_power_rows(prime_limit,max_exponent)
    groups,pairs=prime_pair_squares(rows)
    write('prime_power_grid.json',{'prime_limit':prime_limit,'max_exponent':max_exponent,
          'rows':rows,'square_classes':groups,'class_definition':'ratio is a rational square',
          'complete_in_grid':True,'execution_verified':False})
    write('prime_pair_square_hits.json',{'prime_limit':prime_limit,'max_exponent':max_exponent,
          'distinct_primes':True,'complete_in_grid':True,'globally_complete':False,
          'execution_verified':False,'hits':pairs})
    curves={}
    def add(params,category):
        key=tuple(params)
        if key in curves:
            curves[key]['categories'].append(category); return
        L,u,v,w,z=key
        if u==v==0:
            result=solve(L,0,0,w,z)
        else:
            result=solve_square_leading(*key)
        curves[key]={'coefficients':[z,w,v,u,L*L], 'categories':[category],**result}
    # Every nonzero perturbation in this box has a global coordinate bound.
    for c in range(-25,26):
        for d in range(-20,21):
            if c or d: add((1,0,0,c,d),'linear_box')
    excluded=[]
    for u,v,w,z in itertools.product(range(-2,3),repeat=4):
        try: add((1,u,v,w,z),'quartic_box')
        except ValueError:
            excluded.append([1,u,v,w,z]) # zero normalized perturbation; no finite claim
    for k in range(-200,201):
        add((1,1,1,1,1+k),'repunit_shift')
    catalogue=list(curves.values())
    _,prime_inputs=sigma_sieve(max(r['coordinate_bound'] for r in catalogue))
    prime_inputs=set(prime_inputs)
    shifts=[]
    for i,row in enumerate(catalogue):
        if 'repunit_shift' in row['categories']:
            shifts.append({'shift':row['coefficients'][0]-1,
                'prime_points':[p for p in row['points'] if p[0] in prime_inputs],
                'complete_over_all_primes':True,'python_execution_verified':False,
                'lean_curve':f'PerfectPower.DivisorSumAtlas.curve_{i:04d}_complete',
                'sigma_bridge':'PerfectPower.DivisorSum.shifted_prime_fourth_complete'})
    shifts.sort(key=lambda row:row['shift'])
    write('prime_shift_classifications.json',{'schema':'pp-sigma-prime-shifts/1',
        'rows':shifts,'shifts_with_prime_solutions':sum(bool(r['prime_points']) for r in shifts),
        'signed_prime_points':sum(len(r['prime_points']) for r in shifts),
        'scope':'complete quartic lists, filtered by exact finite primality tests; filtering is Python execution'})
    write('complete_quartics.json',{'schema':'pp-sigma-quartics/1','rows':catalogue,
          'excluded_zero_remainder':excluded,'python_execution_verified':False,
          'scope':'all integer points for each listed equation, via proved family bounds'})
    # Generate reviewable proof-producing Lean commands for the entire catalogue.
    lean=['import PerfectPower.Tactic.LinearPerturbation',
          'import PerfectPower.Tactic.SquareLeadingQuartic',
          'namespace PerfectPower.DivisorSumAtlas',
          'set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    for i,row in enumerate(catalogue):
        p=row['parameters']
        command='native_linear_perturbation' if 'LinearPerturbation' in row['theorem'] else 'native_square_leading_quartic'
        lean.append(f"{command} curve_{i:04d} for "+', '.join(map(str,p)))
        literal='{'+','.join(f'({x},{y})' for x,y in row['points'])+'}' if row['points'] else '∅'
        lean.append(f'theorem curve_{i:04d}_packet : curve_{i:04d} = {literal} := by decide +kernel')
    lean.append('end PerfectPower.DivisorSumAtlas')
    path=out/'CompleteQuartics.lean';path.write_text('\n'.join(lean)+'\n')
    files[path.name]={'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
    chunks=out/'lean_chunks';chunks.mkdir(exist_ok=True)
    for old in chunks.glob('Quartics*.lean'):old.unlink()
    commands=lean[5:-1]
    for start in range(0,len(catalogue),100):
        stop=min(start+100,len(catalogue))
        text=lean[:5]+commands[2*start:2*stop]+[
            f'#print axioms curve_{i:04d}_{suffix}' for i in range(start,stop) for suffix in ('complete','packet')]+[lean[-1]]
        (chunks/f'Quartics{start//100:03d}.lean').write_text('\n'.join(text)+'\n')
    summary={'schema':'pp-sigma-atlas/1','bounded_domain':[1,limit],
             'bounded_hits':{d:len(v) for d,v in hits.items()},
             'prime_limit':prime_limit,'max_exponent':max_exponent,'prime_power_rows':len(rows),'square_classes':len(groups),'prime_pair_square_hits':len(pairs),
             'mixed_nonsquare_factor_hits':sum(not r['both_factors_square'] for r in pairs),
             'complete_quartic_equations':len(catalogue),
             'integer_points_across_equations':sum(len(r['points']) for r in catalogue),
             'empty_quartics':sum(not r['points'] for r in catalogue),
             'excluded_zero_remainder_count':len(excluded),
             'lean_instances_status':'EMITTED_NOT_COMPILED_IN_THIS_RUN',
             'execution_verified':False,'files':files}
    from perfectpower.divisor_sum_view import render
    (out/'results.html').write_text(render(catalogue,pairs,summary))
    write('summary.json',summary)
    return summary

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',default='receipts/divisor_sum')
    parser.add_argument('--limit',type=int,default=1_000_000)
    parser.add_argument('--prime-limit',type=int,default=1000)
    parser.add_argument('--max-exponent',type=int,default=8)
    args=parser.parse_args()
    print(json.dumps(build(args.output,args.limit,args.prime_limit,args.max_exponent),indent=2))
