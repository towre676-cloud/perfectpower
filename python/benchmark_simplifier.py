"""Reproducible integration measurements; these are internal examples, not an independent performance corpus."""
import json
from time import perf_counter
from perfectpower.simplifier import simplify_query,analyze_power,polynomial_pullback


def query(names,atoms):
    return '(set-logic QF_NIA)'+''.join(f'(declare-const {n} Int)' for n in names)+''.join(f'(assert {a})' for a in atoms)+'(check-sat)'

cases=[('coupled_parameter',query('xyz',['(= (* x x) (* y y y))','(= z (+ x 1))','(> z 3)'])),
       ('integer_obstruction',query('xy',['(= (+ (* 2 x) (* 4 y)) 1)'])),
       ('local_residual',query('xy',['(= (* y y) (+ (* x x x) x 1))'])),
       ('noninjective_outer',query('xy',['(= (* x x) (* y y))','(distinct x y)']))]
rows=[]
for name,script in cases:
    start=perf_counter();r=simplify_query(script);elapsed=perf_counter()-start
    rows.append({'name':name,'seconds':elapsed,'variables_removed':sum(s['variables_removed'] for s in r['steps']),
                 'local_relations':len(r['necessary']),'input_bytes':len(script),'residual_bytes':len(r['residual'])})
f=[1,1]+[0]*62+[1];r=analyze_power(f,10,interval=[-1000,1000])
print(json.dumps({'scope':'internal integration measurements; no claimed speedup','queries':rows,
                  'unsupported_global':r['global']['status'],'bounded':r['bounded']['status'],
                  'candidate_statistics':{k:v for k,v in r['bounded'].items() if k in ('interval_size','candidates_checked','sieve_candidates_tested')},
                  'pullback':polynomial_pullback([1,0,0,0,1],[0,1,1])['points']},indent=2))
