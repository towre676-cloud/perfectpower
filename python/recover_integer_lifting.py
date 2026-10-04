"""Rebuild the recovered integral-lift examples and order-map audit.

Run from the repository root: python python/recover_integer_lifting.py.
Optional --z3 checks projected query models against the original formula.
"""
import argparse
import hashlib
import json
from pathlib import Path
from perfectpower.integer_lifting import (smith_certificate,solve_integer,integral_task_section,
    integral_intertwiners,compare_column_lattices,verify_smith)
from perfectpower.integer_projection import project_integer_query
from perfectpower.integral_lattice import smith_invariants,MinorLimit
from perfectpower.exact_linear import task_section,multiply

ROOT=Path(__file__).resolve().parents[1]


def build(output, *, check_z3=False):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    example=solve_integer([[2,3]],[1])
    rational=task_section([[1]],[[2,3]])
    result={'scope':'exact integer computations; no new Lean proof',
            'nonunique_lift':{'rational_constructed_lift':[[str(x) for x in row] for row in rational['lift']],
                             'integer_fibre':example},
            'prime_power_obstruction':solve_integer([[4,0],[0,8]],[0,4]),
            'saturated_kernel':solve_integer([[2,1,1]],[0]),
            'integral_task':integral_task_section([[1,5]],[[2,3]]),
            'integral_intertwiners':integral_intertwiners([[[0,2],[0,0]]],[[[0,3],[0,0]]]),
            'same_smith_different_lattice':compare_column_lattices([[2,0],[0,1]],[[1,0],[0,2]])}
    c=[[0]*4 for _ in range(5)]
    for j,indices in enumerate(((0,),(1,),(2,3),(4,))):
        for i in indices:c[i][j]=1
    inclusion=[row+[0]*4 for row in c]+[[0]*4+row for row in c]
    ambient=[[int(i<5 and j==i+5)-int(i>=5 and j==i-5) for j in range(10)] for i in range(10)]
    pairing=[[int(x) for x in row] for row in multiply(multiply(list(zip(*inclusion)),ambient),inclusion)]
    result['tube_lattice']={'inclusion':smith_certificate(inclusion),'restricted_pairing':smith_certificate(pairing),
            'correction':'The invariant inclusion is primitive. The restricted pairing is non-unimodular, with cokernel C2 x C2. The symmetric sums are primitive ambient vectors.'}
    assert result['tube_lattice']['inclusion']['smith_factors']==[1]*8
    assert result['tube_lattice']['restricted_pairing']['smith_factors']==[1]*6+[2,2]
    # An actual repository dataset, rather than just synthetic matrices.
    packet=json.loads((ROOT/'receipts/order_transports.json').read_text())
    maps=[]
    for entry in packet['embeddings']:
        a=entry['matrix'];cert=smith_certificate(a)
        product=1
        for x in cert['smith_factors']:product*=x
        assert product==entry['index'] and verify_smith(cert)
        witnesses=[]
        for j,col in enumerate(zip(*a)):
            solved=solve_integer(a,col)
            assert solved['particular']==[int(i==j) for i in range(3)]
            witnesses.append(solved['particular'])
        maps.append({'lean':entry['lean'],'index':entry['index'],'smith_factors':cert['smith_factors'],
                     'basis_pullbacks':witnesses,'operation_count':cert['operation_count']})
    result['order_maps']={'count':len(maps),'checked_basis_vectors':3*len(maps),'maps':maps}
    # Twelve equations, eighteen integer variables; exhaustive minors exceed
    # the old default budget, while a constructive reduction returns witnesses.
    wide=[[int(j==i)*(i+1)+int(j==i+6)*(i+1) for j in range(18)] for i in range(12)]
    try:smith_invariants(wide)
    except MinorLimit:old='MINOR_BUDGET_EXCEEDED'
    else:old='COMPLETE'
    solved=solve_integer(wide,[sum(row) for row in wide])
    result['wide_presentation']={'shape':[12,18],'old_minor_status':old,'solution':solved}
    assert old=='MINOR_BUDGET_EXCEEDED' and solved['status']=='INTEGER_AFFINE_FIBRE'
    bodies={
        'alternative_integer_lift':('(assert (= (+ (* 2 x) (* 3 y)) 1))(assert (= (* x x) 1))','sat'),
        'prime_power_hidden_obstruction':('(assert (= (+ (* 4 x) (* 8 y)) 2))(assert (> (* x x) 0))','unsat'),
        'residual_conflict':('(assert (= (+ (* 2 x) (* 3 y)) 1))(assert (= x 2))(assert (= y 0))','unsat'),
        'modular_residual':('(assert (= (+ x y) 4))(assert (= (mod x 3) 1))(assert (> y 0))','sat')}
    queries=[]
    for name,(body,expected) in bodies.items():
        source='(set-logic QF_NIA)\n(declare-const x Int)\n(declare-const y Int)\n'+body+'\n(check-sat)\n'
        projected=project_integer_query(source)
        (output/f'{name}.original.smt2').write_text(source)
        (output/f'{name}.projected.smt2').write_text(projected.smt)
        ledger={'name':name,'expected':expected,'linear':projected.linear,'parameters':projected.parameters,
                'bindings':projected.bindings,'solution':projected.solution}
        if check_z3:
            import z3
            original_solver,projected_solver=z3.Solver(),z3.Solver()
            for solver,script in ((original_solver,source),(projected_solver,projected.smt)):
                solver.set(timeout=2000);solver.add(z3.parse_smt2_string(script))
            old_status,new_status=str(original_solver.check()),str(projected_solver.check())
            assert old_status==new_status==expected
            ledger['solver']={'version':z3.get_version_string(),'original':old_status,'projected':new_status}
            if new_status=='sat':
                model=projected_solver.model()
                values={p:model.eval(z3.Int(p),model_completion=True).as_long() for p in projected.parameters}
                lift=projected.lift(values)
                original_solver.add(*[z3.Int(n)==v for n,v in lift.items()]);assert original_solver.check()==z3.sat
                ledger['solver']['lifted_model']=lift
                ledger['solver']['model_replayed_on_original']=True
        queries.append(ledger)
    result['queries']=queries
    result['input_sha256']={str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest()
                            for path in (ROOT/'receipts/order_transports.json',ROOT/'docs/OPERATOR_RECOVERY_MONOGRAPH.md')}
    (output/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    return {'order_maps':len(maps),'basis_vectors':3*len(maps),'queries':len(queries),
            'wide_parameters':solved['parameter_count'],'z3_checked':check_z3,'output':str(output)}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=ROOT/'receipts/integer_lifting')
    p.add_argument('--z3',action='store_true')
    args=p.parse_args();print(json.dumps(build(args.output,check_z3=args.z3),indent=2))
