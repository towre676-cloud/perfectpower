"""Three end-to-end examples, with complete-source reductions and raw timings.

This is a curated demonstration, not an industrial benchmark corpus.
"""
import json
from pathlib import Path
from time import perf_counter
from hashlib import sha256
from .centered_divisor import shift_polynomial,emit_lean_instance,solve_centered
from .compiler import compile_constraint,PowerConstraint,pmul
from .finite_formula import emit_finite_query
from .finite_projection import project_finite_query
from .square_triangular_queries import query,select,point

OFFSET=10**30
FILTERS=(('index',97,1),('root',5,1))


def _mordell_script(shift,k,extras,*,xscale=1,xoffset=0,yscale=1,yoffset=0):
    def num(v):return str(v) if v>=0 else f'(- {-v})'
    x=f'(+ (* {num(xscale)} x) {num(xoffset-shift)})'
    y=f'(+ (* {num(yscale)} y) {num(yoffset)})'
    return f'''(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(assert (= (* {y} {y}) (+ (* {x} {x} {x}) {num(k)})))
{extras}
(check-sat)
'''


def constraint_cases():
    h=OFFSET
    yield 'mordell_beyond_last_point',_mordell_script(h,17,f'(assert (>= x {h+5235}))'),'unsat'
    yield 'mordell_witness_with_extra_variables',_mordell_script(h,17,f'''(assert (= x {h+5234}))
(assert (>= y 0))
(assert (= z (+ (- x {h}) y)))
(assert (= w (+ (* 2 z) 1)))
(assert (> w 100000))'''),'sat'
    yield 'mordell_extra_variable_conflict',_mordell_script(h,17,f'''(assert (= x {h+5234}))
(assert (>= y 0))
(assert (= z (+ (- x {h}) y)))
(assert (= w (+ (* 2 z) 1)))
(assert (<= w 1000))'''),'unsat'
    yield 'mordell_small_positive_witness',_mordell_script(h,17,f'''(assert (> x {h}))
(assert (< y 10))
(assert (> y 0))
(assert (= z (* (- x {h}) y)))
(assert (= w (+ z 1)))'''),'sat'
    yield 'mordell_integral_image_empty',_mordell_script(0,22,'',xscale=6,xoffset=1),'unsat'
    yield 'quartic_product_conflict','''(set-logic QF_NIA)
(declare-const x Int)(declare-const y Int)(declare-const z Int)(declare-const w Int)
(assert (= (* y y) (+ (* 3 x x x x) (* 3 x x) 1)))
(assert (= w (* x z)))
(assert (not (= w 0)))
(check-sat)
''','unsat'


def _serialize(value):return json.dumps(value,indent=2,default=str)+'\n'


def build_examples(output):
    """Build reviewable scripts, emitted proof sources and exact result packets."""
    out=Path(output);out.mkdir(parents=True,exist_ok=True);(out/'queries').mkdir(exist_ok=True);(out/'lean').mkdir(exist_ok=True)
    canonical=(0,-2,0,2);p=shift_polynomial(canonical,-OFFSET);f=list(pmul(p,p));f[0]+=25
    start=perf_counter();plan=compile_constraint(PowerConstraint(tuple(f),2));compile_seconds=perf_counter()-start
    points=[(n,y) for n,roots in plan.all_hits() for y in roots]
    expected=[(OFFSET+t,y) for t in (-2,-1,0,1,2) for y in ((-13,13) if abs(t)==2 else (-5,5))]
    if points!=sorted(expected):raise AssertionError('hidden-needle complete list mismatch')
    result=solve_centered(p,25)
    if result['points']!=points:raise AssertionError('positive compiler list disagrees with all-integer solve')
    (out/'lean/HiddenNeedle.lean').write_text(emit_lean_instance(result))
    # The generated standalone program consumes the same COMPLETE_FINITE plan.
    from .specialize import LoopProgram,specialize
    expression=f'(2*(n-{OFFSET})**3-2*(n-{OFFSET}))**2+25'
    specialization=specialize(LoopProgram(expression,('power',2)))
    standalone=specialization.source
    if standalone is None:raise AssertionError('missing standalone finite program')
    (out/'hidden_needle_original.py').write_text(specialization.original)
    (out/'hidden_needle_program.py').write_text(standalone)
    baseline_limit=100000
    start=perf_counter();baseline=specialization.run_original(baseline_limit);baseline_seconds=perf_counter()-start
    start=perf_counter();fast_prefix=specialization.run_specialized(baseline_limit);fast_prefix_seconds=perf_counter()-start
    if baseline!=fast_prefix:raise AssertionError('bounded original/specialized mismatch')
    namespace={};exec(standalone,namespace)
    replay=namespace['run'](OFFSET+10)
    if [(n,y) for n,roots in replay for y in roots]!=points:raise AssertionError('standalone replay mismatch')
    sparse=query(10**1000,FILTERS);selected=select(27,FILTERS);next_selected=select(28,FILTERS)
    if selected['point'][0]>10**1000 or next_selected['point'][0]<=10**1000:
        raise AssertionError('filtered boundary mismatch')
    reductions=[]
    for name,source,expected_status in constraint_cases():
        start=perf_counter();emission=emit_finite_query(source);reduction_seconds=perf_counter()-start
        start=perf_counter();projected=project_finite_query(source);projection_seconds=perf_counter()-start
        (out/'queries'/f'{name}.projected.smt2').write_text(projected.smt)
        source_file=out/'queries'/f'{name}.smt2';source_file.write_text(source)
        (out/'queries'/f'{name}.reduced.smt2').write_text(emission.smt)
        (out/'lean'/f'{name}.lean').write_text(emission.lean)
        reductions.append({'name':name,'family':emission.family,'expected':expected_status,
                           'source_sha256':emission.source_sha256,'source_points':emission.points,
                           'reduction_seconds':reduction_seconds,'projection_seconds':projection_seconds,
                           'remaining_symbols':list(emission.remaining_symbols),
                           'eliminated_symbols':list(emission.eliminated_symbols),
                           'projected_linear':projected.linear,'lean_instance_status':'EMITTED_NOT_COMPILED_IN_THIS_RUN'})
    report={'schema':'pp-showcase/1','execution_verified':False,
            'hidden_needle':{'offset':OFFSET,'expression':expression,'expanded_coefficients':f,
                'complete_points':points,'all_integer_solve':result,'positive_indices':len({n for n,y in points}),
                'plan':plan.explain(),'compile_seconds':compile_seconds,'standalone_replayed':True,
                'coordinate_range_searched':False,
                'bounded_prefix_comparison':{'bound':baseline_limit,'hits':baseline,
                    'original_seconds':baseline_seconds,'specialized_seconds':fast_prefix_seconds,
                    'scope':'equal bounded prefix outputs; original prefix is not a complete global answer'},'new_lean_instance_status':'EMITTED_NOT_COMPILED_IN_THIS_RUN'},
            'square_triangular':{'query':sparse,'last_filtered':selected,'next_filtered':next_selected,
                'first_ten':[point(j) for j in range(1,11)],
                'all_integer_sizes_scanned':False},
            'whole_queries':reductions,'scope':'curated complete-family demonstrations; no industrial speedup claim'}
    (out/'results.json').write_text(_serialize(report));return report


def benchmark_queries(output,*,timeout_ms=2000,repeats=3):
    """Measure original vs reduced queries with fresh installed Z3 solvers.

    Both decisive results must match the independently specified case answer.
    Unknown/timeouts are retained, never counted as solved.
    """
    import z3
    if type(timeout_ms) is not int or timeout_ms<1 or type(repeats) is not int or repeats<1:
        raise ValueError('positive timeout and repetition count required')
    out=Path(output);ledger=[]
    for name,source,expected in constraint_cases():
        reduced=(out/'queries'/f'{name}.reduced.smt2').read_text()
        projected=(out/'queries'/f'{name}.projected.smt2').read_text()
        emission=emit_finite_query(source)
        for repetition in range(repeats):
            # Alternate order so one variant does not always receive the warm run.
            variants=(('original',source),('reduced',reduced),('projected',projected))
            if repetition%2:variants=tuple(reversed(variants))
            for variant,text in variants:
                start=perf_counter();assertions=z3.parse_smt2_string(text);parse_seconds=perf_counter()-start
                solver=z3.Solver();solver.set(timeout=timeout_ms,random_seed=100+repetition);solver.add(assertions)
                start=perf_counter();answer=solver.check();solve_seconds=perf_counter()-start
                status=str(answer);model=None
                if status in ('sat','unsat') and status!=expected:raise AssertionError(f'wrong answer: {name} {variant}')
                if status=='sat':
                    model={str(d):str(solver.model()[d]) for d in solver.model().decls()}
                    # Recheck the complete supplied model against the ORIGINAL formula.
                    bindings=[(z3.Int(k),z3.IntVal(v)) for k,v in model.items()]
                    original=z3.And(list(z3.parse_smt2_string(source)))
                    if variant=='projected':
                        candidates=[]
                        for a,b in emission.points:
                            point_bindings=bindings+[(z3.Int(emission.eliminated_symbols[0]),z3.IntVal(a)),
                                                     (z3.Int(emission.eliminated_symbols[1]),z3.IntVal(b))]
                            if z3.is_true(z3.simplify(z3.substitute(original,*point_bindings))):candidates.append((a,b))
                        if not candidates:raise AssertionError('projected SAT model has no original witness')
                        a,b=candidates[0];model.update(dict(zip(emission.eliminated_symbols,map(str,(a,b)))))
                    else:
                        evaluated=z3.simplify(z3.substitute(original,*bindings))
                        if not z3.is_true(evaluated):raise AssertionError('SAT model does not replay on original query')
                ledger.append({'case':name,'variant':variant,'repetition':repetition,'expected':expected,
                               'status':status,'parse_seconds':parse_seconds,'solve_seconds':solve_seconds,
                               'reason_unknown':solver.reason_unknown() if status=='unknown' else None,'model':model})
    summary={variant:{'decisive':sum(x['status']!='unknown' for x in ledger if x['variant']==variant),
                      'trials':sum(x['variant']==variant for x in ledger),
                      'summed_solve_seconds':sum(x['solve_seconds'] for x in ledger if x['variant']==variant),
                      'summed_parse_seconds':sum(x['parse_seconds'] for x in ledger if x['variant']==variant)}
             for variant in ('original','reduced','projected')}
    report={'schema':'pp-showcase-timing/1','z3_version':z3.get_version_string(),'timeout_ms':timeout_ms,
            'repeats':repeats,'ledger':ledger,'summary':summary,
            'scope':'six curated examples, local fresh solvers; excludes proof-generation time and does not imply industrial speedup',
            'execution_verified':False}
    (out/'timings.json').write_text(_serialize(report));return report
