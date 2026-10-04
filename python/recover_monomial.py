"""Rebuild the August 2025 multiplicative recovery and current corpus replay."""
import argparse
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
from perfectpower.monomial import (OLD_MATRIX,recovered_2025_packet,solve_monomial,
                                  solve_rational_monomial)
from perfectpower.integral_lattice import smith_invariants
from perfectpower.monomial_projection import project_monomial_query

ROOT=Path(__file__).resolve().parents[1]


def build(output,check_z3=False):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    historical=recovered_2025_packet();independent=smith_invariants(OLD_MATRIX)
    assert independent['smith_factors']==historical['corrected_smith_factors']
    historical['independent_determinantal_divisors']=independent
    historical['compatible_rational_fibre']=solve_rational_monomial(OLD_MATRIX,[1,1,8,1])
    historical['incompatible_cube_rhs']=solve_rational_monomial(OLD_MATRIX,[1,1,2,1])
    assert historical['incompatible_cube_rhs']['obstruction']['modulus']==3
    result={'scope':'Exact arithmetic on recovered equations; no empirical Standard Model law or Weyl symmetry inferred.',
            'historical':historical,
            'finite_square_cube':solve_monomial([[2,3]],[2**20*3**12]),
            'signed_exponents':solve_monomial([[2,-3],[1,1]],[Q(4,27),6]),
            'huge_exact_power':solve_monomial([[3]],[(10**100+37)**3])}
    grid_path=ROOT/'receipts/divisor_sum/prime_power_grid.json'
    joins_path=ROOT/'receipts/divisor_sum/prime_pair_square_hits.json'
    grid=json.loads(grid_path.read_text())['rows'];joins=json.loads(joins_path.read_text())['hits']
    recovered_grid=[]
    for row in grid:
        answer=solve_monomial([[row['exponent']]],[row['n']])
        assert answer['points']==[[row['prime']]]
        recovered_grid.append({'n':row['n'],'exponent':row['exponent'],'recovered_prime':answer['points'][0][0]})
    recovered_joins=[]
    for row in joins:
        answer=solve_monomial([[2]],[row['sigma']])
        assert answer['points']==[[row['root']]]
        recovered_joins.append({'p':row['p'],'a':row['a'],'q':row['q'],'b':row['b'],
                                'sigma':row['sigma'],'recovered_root':answer['points'][0][0]})
    result['current_corpus']={'prime_power_rows':len(grid),'square_product_joins':len(joins),
                             'recovered_grid':recovered_grid,'recovered_joins':recovered_joins,
                             'scope':'Every stored row replays. This does not extend the bounded sigma corpus to a global classification.'}
    prefix='(set-logic QF_NIA)\n(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n(assert (> x 0))\n(assert (> y 0))\n'
    cases={
        'product_with_free_residual':('(assert (= (* x y) 12))\n(assert (= z (* x y)))','sat'),
        'product_residual_conflict':('(assert (= (* x y) 12))\n(assert (= z (* x y)))\n(assert (> z 12))','unsat'),
        'square_cube_obstruction':('(assert (= (* x x y y y) 2))\n(assert (> z (* x y)))','unsat'),
        'nonlinear_residual_retained':('(assert (= (* x y) 12))\n(assert (= (* z z) x))\n(assert (> z 1))','sat')}
    queries=[]
    for name,(body,expected) in cases.items():
        source=prefix+body+'\n(check-sat)\n';r=project_monomial_query(source)
        (output/f'{name}.original.smt2').write_text(source)
        (output/f'{name}.projected.smt2').write_text(r.smt)
        item={'name':name,'expected':expected,'linear':r.linear,'points':r.points,
              'eliminated':r.eliminated_symbols,'remaining':r.remaining_symbols,'solution':r.solution}
        if check_z3:
            import z3
            original,projected=z3.Solver(),z3.Solver()
            for solver,script in ((original,source),(projected,r.smt)):
                solver.set(timeout=2000);solver.add(z3.parse_smt2_string(script))
            a,b=str(original.check()),str(projected.check());assert a==b==expected
            item['solver']={'version':z3.get_version_string(),'original':a,'projected':b}
            if b=='sat':
                model=projected.model()
                extra={n:model.eval(z3.Int(n),model_completion=True).as_long() for n in r.remaining_symbols}
                lifted=None
                for point in r.points:
                    candidate={**dict(zip(r.eliminated_symbols,point)),**extra}
                    original.push();original.add(*[z3.Int(n)==v for n,v in candidate.items()])
                    survives=original.check()==z3.sat;original.pop()
                    if survives:lifted=candidate;break
                assert lifted is not None;item['solver']['lifted_model']=lifted
                item['solver']['model_replayed_on_original']=True
        queries.append(item)
    result['queries']=queries
    result['input_sha256']={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest()
                            for path in (grid_path,joins_path)}
    (output/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    return {'historical_smith':[1,1,1,3],'hidden_variable_relations':2,
            'finite_square_cube_points':len(result['finite_square_cube']['points']),
            'prime_power_replays':len(grid),'square_product_replays':len(joins),
            'queries':len(queries),'z3_checked':check_z3}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=ROOT/'receipts/monomial_recovery')
    p.add_argument('--z3',action='store_true')
    args=p.parse_args();print(json.dumps(build(args.output,args.z3),indent=2))
