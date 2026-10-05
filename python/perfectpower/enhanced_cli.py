"""Integrated structural solving and exact closest integer observations."""
import json
from fractions import Fraction as Q
from .deep_recovery_cli import exact_json


def add_commands(sub):
    p=sub.add_parser('box-faces',help='complete bounded integer models from affine elimination and Bernstein zero faces')
    p.add_argument('--equations',type=json.loads,required=True);p.add_argument('--box',type=json.loads,required=True)
    p.add_argument('--verify',action='store_true')
    p=sub.add_parser('box-exclude',help='exact bivariate ideal separators and necessary residual boxes')
    p.add_argument('--equations',type=json.loads,required=True);p.add_argument('--box',type=json.loads,required=True)
    p.add_argument('--weights',type=json.loads);p.add_argument('--depth',type=int,default=4)
    p.add_argument('--node-limit',type=int,default=10000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('metric-box',help='exact pointwise hyperelliptic chart metric brackets')
    p.add_argument('--coeff',type=json.loads,required=True);p.add_argument('--chart',choices=('finite','branch','infinity'),required=True)
    p.add_argument('--branch');p.add_argument('--box',type=json.loads,required=True)
    p.add_argument('--scales',type=json.loads,required=True);p.add_argument('--density',default='1')
    p.add_argument('--depth',type=int,default=4);p.add_argument('--node-limit',type=int,default=10000)
    p.add_argument('--verify',action='store_true')
    p=sub.add_parser('family-evaluate',help='complete per-parameter evaluation of composed arithmetic generators')
    p.add_argument('--coeff',type=json.loads,required=True);p.add_argument('--d',type=int,default=2);p.add_argument('--parameter',type=int,required=True)
    p.add_argument('--node-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('semilinear-domain',help='complete polynomial/modular integer domains, exact counts and rank selection')
    p.add_argument('--predicate',type=json.loads,required=True);p.add_argument('--interval',type=json.loads);p.add_argument('--select',type=int)
    p.add_argument('--start',type=int,default=0);p.add_argument('--period-limit',type=int,default=65536);p.add_argument('--node-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('semilinear-optimize',help='global polynomial min/max on complete congruence-restricted integer domains')
    p.add_argument('--predicate',type=json.loads,default=True);p.add_argument('--objective',type=json.loads,required=True)
    p.add_argument('--sense',choices=('min','max'),default='min');p.add_argument('--period-limit',type=int,default=65536);p.add_argument('--node-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('polynomial-charts',help='complete signed power-curve families with integer coordinate images and nonlinear fibres')
    p.add_argument('--left',type=json.loads,required=True);p.add_argument('--right',type=json.loads,required=True)
    p.add_argument('--parameter',type=int);p.add_argument('--node-limit',type=int,default=100000);p.add_argument('--period-limit',type=int,default=65536);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('curve-query',help='exact power-curve counts and global bivariate polynomial optimization without box scanning')
    p.add_argument('--left',type=json.loads,required=True);p.add_argument('--right',type=json.loads,required=True);p.add_argument('--predicate',type=json.loads,default=True)
    p.add_argument('--objective');p.add_argument('--sense',choices=('min','max'),default='min');p.add_argument('--point-limit',type=int,default=128)
    p.add_argument('--node-limit',type=int,default=100000);p.add_argument('--period-limit',type=int,default=65536);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('gamma-domain',help='complete natural-index sign domains of normalized fixed Gamma/product/binomial expressions')
    p.add_argument('--predicate',type=json.loads,default=True)
    p.add_argument('--spec',type=json.loads,required=True);p.add_argument('--relation',choices=('=','!=','<','<=','>','>='),default='>=')
    p.add_argument('--threshold',default='0');p.add_argument('--node-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('gamma-optimize',help='global exact rational optimum and every natural-index tie for fixed expressions')
    p.add_argument('--spec',type=json.loads,required=True);p.add_argument('--predicate',type=json.loads,default=True)
    p.add_argument('--sense',choices=('min','max'),default='min');p.add_argument('--node-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('polynomial-domain',help='complete Boolean polynomial constraints over all integers as interval unions')
    p.add_argument('--predicate',type=json.loads,required=True);p.add_argument('--node-limit',type=int,default=100000)
    p.add_argument('--verify',action='store_true')
    p=sub.add_parser('polynomial-optimize',help='exact global integer polynomial min/max including every tie')
    p.add_argument('--predicate',type=json.loads,default=True);p.add_argument('--objective',type=json.loads,required=True)
    p.add_argument('--sense',choices=('min','max'),default='min');p.add_argument('--node-limit',type=int,default=100000)
    p.add_argument('--verify',action='store_true')
    p=sub.add_parser('polynomial-decompose',help='discover rational functional decompositions through exact polynomial coordinates')
    p.add_argument('--coeff',type=json.loads,required=True);p.add_argument('--algebra-limit',type=int,default=2000000)
    p=sub.add_parser('polynomial-relation',help='complete two-sided polynomial equations through quadratic and power transport')
    p.add_argument('--left',type=json.loads,required=True);p.add_argument('--right',type=json.loads,required=True)
    p.add_argument('--work-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('integral-machine',help='minimal integer state realization preserving future outputs and observation divisibility')
    p.add_argument('--operators',type=json.loads,required=True);p.add_argument('--seed',type=json.loads,required=True)
    p.add_argument('--readouts',type=json.loads,required=True);p.add_argument('--word',type=json.loads,default=[])
    p.add_argument('--order',choices=('execution','written'),default='execution');p.add_argument('--observations',type=json.loads)
    p.add_argument('--verify',action='store_true')
    p=sub.add_parser('gamma-analyze',help='exact Gamma/product normalization, factorial valuations and hypergeometric transport')
    p.add_argument('--spec',type=json.loads,required=True);p.add_argument('--d',type=int,default=2)
    p.add_argument('--n',type=int);p.add_argument('--interval',type=json.loads)
    p.add_argument('--complete',action='store_true');p.add_argument('--work-limit',type=int,default=100000)
    p.add_argument('--verify',action='store_true')
    p=sub.add_parser('gamma-unit',help='factorial-ratio valuation and stripped-unit power obstruction')
    p.add_argument('--numerator',type=json.loads,required=True);p.add_argument('--denominator',type=json.loads,required=True)
    p.add_argument('--n',type=int,required=True);p.add_argument('--d',type=int,default=2)
    p.add_argument('--prime',type=int,required=True);p.add_argument('--depth',type=int,default=3)
    p.add_argument('--work-limit',type=int,default=100000)
    p=sub.add_parser('beta-period',help='exact symbolic Beta/Gamma reference for a symmetric branch integral')
    p.add_argument('--m',type=int,required=True)
    p=sub.add_parser('finite-mellin',help='exact integer Mellin value of a finite positive hit set')
    p.add_argument('--indices',type=json.loads,required=True);p.add_argument('--s',type=int,required=True)
    p=sub.add_parser('witness-resolvent',help='certify the rational generating functions of exact matrix outputs')
    p.add_argument('--matrix',type=json.loads,required=True);p.add_argument('--seed',type=json.loads,required=True)
    p.add_argument('--readouts',type=json.loads,required=True);p.add_argument('--index',type=int,default=100)
    p.add_argument('--offset',type=int,default=0);p.add_argument('--step',type=int,default=1);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('connection-reweight',help='repair graph measures through a small exact defect matrix')
    p.add_argument('--vertices',type=int,required=True);p.add_argument('--edges',type=json.loads,required=True)
    p.add_argument('--power',type=int,required=True);p.add_argument('--weights',type=json.loads,required=True)
    p.add_argument('--new-weights',type=json.loads,required=True);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('simplify-query',help='compose exact reductions and retain the residual SMT query')
    p.add_argument('--script',required=True);p.add_argument('--branch-limit',type=int,default=128)
    p.add_argument('--model',type=json.loads,help='lift a residual integer model back to an original witness')
    p.add_argument('--verify',action='store_true')
    p=sub.add_parser('analyze-power',help='global result, necessary residues and optional complete bounded query')
    p.add_argument('--coeff',type=json.loads,required=True);p.add_argument('--d',type=int,default=2)
    p.add_argument('--interval',type=json.loads);p.add_argument('--work-limit',type=int,default=100000)
    p.add_argument('--question',type=json.loads);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('polynomial-pullback',help='lift a complete outer solve through all integer polynomial fibres')
    p.add_argument('--outer',type=json.loads,required=True);p.add_argument('--inner',type=json.loads,required=True)
    p.add_argument('--d',type=int,default=2);p.add_argument('--work-limit',type=int,default=100000)
    p.add_argument('--verify',action='store_true')
    p=sub.add_parser('observable-machine',help='minimal exact state machine preserving all supplied operator-word outputs')
    p.add_argument('--operators',type=json.loads,required=True);p.add_argument('--seed',type=json.loads,required=True)
    p.add_argument('--readouts',type=json.loads,required=True);p.add_argument('--word',type=json.loads,default=[])
    p.add_argument('--order',choices=('execution','written'),default='execution');p.add_argument('--verify',action='store_true')
    p=sub.add_parser('recurrence-batch',help='share a minimal exact machine across supplied recurrence definitions')
    p.add_argument('--models',type=json.loads,required=True);p.add_argument('--index',type=int,default=100)
    p.add_argument('--verify',action='store_true')
    p=sub.add_parser('factored-scan',help='complete bounded power search with prime-power depth filters')
    p.add_argument('--coeff',type=json.loads,required=True);p.add_argument('--d',type=int,default=2)
    p.add_argument('--lo',type=int,required=True);p.add_argument('--hi',type=int,required=True)
    p.add_argument('--factors',type=json.loads);p.add_argument('--work-limit',type=int,default=100000)
    p.add_argument('--filter-limit',type=int,default=2000000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('exact-solve',help='all-integer structural solve with replayable finite-leaf certificate')
    p.add_argument('--coeff',type=json.loads,required=True);p.add_argument('--d',type=int,default=2)
    p.add_argument('--work-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('nearest-lift',help='all closest integer points satisfying exact linear observations')
    p.add_argument('--matrix',type=json.loads,required=True);p.add_argument('--rhs',type=json.loads,required=True)
    p.add_argument('--target',type=json.loads,required=True);p.add_argument('--mass',type=json.loads)
    p.add_argument('--node-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('integer-roots',help='complete integer polynomial roots with a budgeted Sturm certificate')
    p.add_argument('--coeff',type=json.loads,required=True);p.add_argument('--lo',type=int);p.add_argument('--hi',type=int)
    p.add_argument('--node-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('square-fibres',help='complete square-plus-constant solve using certified Sturm fibres')
    p.add_argument('--coeff',type=json.loads,required=True);p.add_argument('--k',type=int,required=True)
    p.add_argument('--work-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('connection-measure',help='exact basis events without enumerating every graph basis')
    p.add_argument('--vertices',type=int,required=True);p.add_argument('--edges',type=json.loads,required=True)
    p.add_argument('--power',type=int,required=True);p.add_argument('--weights',type=json.loads)
    p.add_argument('--include',type=json.loads,default=[]);p.add_argument('--exclude',type=json.loads,default=[])
    p.add_argument('--verify',action='store_true')

    p=sub.add_parser('coefficient-charts',help='primitive signed charts for c*x^p=d*y^q')
    p.add_argument('--c',type=int,required=True);p.add_argument('--p',type=int,required=True)
    p.add_argument('--d',type=int,required=True);p.add_argument('--q',type=int,required=True)
    p.add_argument('--factor-limit',type=int,default=100000);p.add_argument('--verify',action='store_true')
    p=sub.add_parser('recurrence-orbit',help='exact modular polynomial-coefficient orbit and hit domain')
    p.add_argument('--p',type=json.loads,required=True);p.add_argument('--q',type=json.loads,required=True)
    p.add_argument('--modulus',type=int,required=True);p.add_argument('--seed',type=int,required=True)
    p.add_argument('--power',type=int,default=2);p.add_argument('--step-limit',type=int,default=100000)
    p.add_argument('--objective',type=json.loads);p.add_argument('--sense',choices=['min','max'],default='min')
    p.add_argument('--through',type=int);p.add_argument('--rank',type=int);p.add_argument('--verify',action='store_true')

    p=sub.add_parser('operator-algebra',help='exact generated algebra, commutant and double-commutant certificates')
    p.add_argument('--operators',type=json.loads,required=True);p.add_argument('--verify',action='store_true')


def dispatch(args):
    if args.command=='box-faces':
        from .bernstein_boxes import solve_affine_faces,verify_affine_faces
        p=solve_affine_faces(args.equations,args.box)
        if args.verify and not verify_affine_faces(p):raise ValueError('face-model replay failed')
        print(json.dumps(p,indent=2));return True
    if args.command=='box-exclude':
        from .bernstein_boxes import compile_system,candidate_boxes,verify_exclusion
        p=(compile_system(args.equations,args.box,depth=args.depth,node_limit=args.node_limit)
           if args.weights is None else candidate_boxes(args.equations,args.weights,args.box,depth=args.depth,node_limit=args.node_limit))
        if args.verify and not verify_exclusion(p):raise ValueError('exclusion replay failed')
        print(json.dumps(p,indent=2));return True
    if args.command=='metric-box':
        from .metric_boxes import compare,verify
        p=compare(args.coeff,args.chart,args.box,*args.scales,args.density,args.branch,depth=args.depth,node_limit=args.node_limit)
        if args.verify and not verify(p):raise ValueError('metric replay failed')
        print(json.dumps(p,indent=2));return True

    if args.command=='coefficient-charts':
        from .coefficient_charts import primitive_power_charts,verify_primitive_charts
        result=primitive_power_charts(args.c,args.p,args.d,args.q,factor_limit=args.factor_limit)
        if args.verify:result['certificate_replay']=verify_primitive_charts(result,factor_limit=args.factor_limit)
    elif args.command=='recurrence-orbit':
        from .recurrence_domains import recurrence_orbit,orbit_domain,orbit_count,orbit_select,verify_orbit_domain,orbit_optimize
        result=orbit_domain(recurrence_orbit(args.p,args.q,args.modulus,args.seed,step_limit=args.step_limit),power=args.power)
        if args.verify:result['certificate_replay']=verify_orbit_domain(result,step_limit=args.step_limit)
        if args.through is not None:result['count']=orbit_count(result,0,args.through)
        if args.rank is not None:result['selected_index']=orbit_select(result,args.rank)
        if args.objective is not None:result['optimization']=orbit_optimize(json.loads(json.dumps(result)),args.objective,sense=args.sense)
    elif args.command=='family-evaluate':
        from .arithmetic_engine import ArithmeticEngine
        from .arithmetic_families import family_points,verify_family_evaluation
        source=ArithmeticEngine(work_limit=args.node_limit).solve(args.coeff,args.d)
        result={'solution':source,'evaluation':None}
        if source['status']=='GENERATOR':
            result['evaluation']=family_points(source,args.parameter,node_limit=args.node_limit)
            if args.verify:result['certificate_replay']=verify_family_evaluation(source,result['evaluation'],node_limit=args.node_limit)
    elif args.command=='semilinear-domain':
        from .semilinear_domains import semilinear_domain,count_domain,select,verify_domain
        result=semilinear_domain(args.predicate,node_limit=args.node_limit,period_limit=args.period_limit)
        if args.interval is not None:
            if not isinstance(args.interval,list) or len(args.interval)!=2:raise ValueError('closed interval pair required')
            result['query_count']=count_domain(result,*args.interval)
        if args.select is not None:result['selected']=select(result,args.select,start=args.start)
        if args.verify:result['certificate_replay']=verify_domain(result,node_limit=args.node_limit,period_limit=args.period_limit)
    elif args.command=='semilinear-optimize':
        from .semilinear_domains import optimize_semilinear,verify_optimization
        result=optimize_semilinear(args.predicate,args.objective,sense=args.sense,node_limit=args.node_limit,period_limit=args.period_limit)
        if args.verify:result['certificate_replay']=verify_optimization(result,node_limit=args.node_limit,period_limit=args.period_limit)
    elif args.command=='polynomial-charts':
        from .polynomial_charts import parameterize_relation,verify_parameterization,evaluate_parameterization,verify_evaluation
        result=parameterize_relation(args.left,args.right,node_limit=args.node_limit,period_limit=args.period_limit)
        if args.parameter is not None:result['evaluation']=evaluate_parameterization(result,args.parameter,node_limit=args.node_limit)
        if args.verify and args.parameter is not None:result['evaluation_replay']=verify_evaluation(result,result['evaluation'],node_limit=args.node_limit)
        if args.verify:result['certificate_replay']=verify_parameterization(result,node_limit=args.node_limit,period_limit=args.period_limit)
    elif args.command=='curve-query':
        from .curve_queries import query_curve,verify_curve_query
        result=query_curve(args.left,args.right,args.predicate,objective=args.objective,sense=args.sense,point_limit=args.point_limit,node_limit=args.node_limit,period_limit=args.period_limit)
        if args.verify:result['certificate_replay']=verify_curve_query(result,node_limit=args.node_limit,period_limit=args.period_limit)
    elif args.command=='gamma-domain':
        from .gamma_polynomial import gamma_domain,verify_gamma_domain
        result=gamma_domain(args.spec,args.relation,args.threshold,predicate=args.predicate,node_limit=args.node_limit)
        if args.verify:result['certificate_replay']=verify_gamma_domain(result,node_limit=args.node_limit)
    elif args.command=='gamma-optimize':
        from .gamma_polynomial import optimize_gamma,verify_gamma_optimum
        result=optimize_gamma(args.spec,args.predicate,sense=args.sense,node_limit=args.node_limit)
        if args.verify:result['certificate_replay']=verify_gamma_optimum(result,node_limit=args.node_limit)
    elif args.command=='polynomial-domain':
        from .polynomial_domains import integer_domain,verify_domain
        result=integer_domain(args.predicate,node_limit=args.node_limit)
        if args.verify:result['certificate_replay']=verify_domain(result,node_limit=args.node_limit)
    elif args.command=='polynomial-optimize':
        from .polynomial_domains import optimize_polynomial,verify_optimization
        result=optimize_polynomial(args.predicate,args.objective,sense=args.sense,node_limit=args.node_limit)
        if args.verify:result['certificate_replay']=verify_optimization(result,node_limit=args.node_limit)
    elif args.command=='polynomial-decompose':
        from .polynomial_composition import discover_decompositions
        result=discover_decompositions(args.coeff,algebra_limit=args.algebra_limit)
    elif args.command=='polynomial-relation':
        from .polynomial_relations import solve_relation,verify_relation
        result=solve_relation(args.left,args.right,work_limit=args.work_limit)
        if args.verify:result['certificate_replay']=verify_relation(result,work_limit=args.work_limit)
    elif args.command=='integral-machine':
        from .integral_machine import integral_machine,integral_word_output,observation_fibre,verify_integral_machine
        result=integral_machine(args.operators,args.seed,args.readouts)
        result['output']=integral_word_output(result,args.word,order=args.order)
        if args.observations is not None:result['observation_fibre']=observation_fibre(result,args.observations)
        if args.verify:result['certificate_replay']=verify_integral_machine(result)
    elif args.command=='gamma-analyze':
        from .gamma_arithmetic import analyze_gamma,verify_gamma
        result=analyze_gamma(args.spec,args.d,n=args.n,interval=args.interval,complete=args.complete,work_limit=args.work_limit)
        if args.verify:result['certificate_replay']=verify_gamma(result)
    elif args.command=='gamma-unit':
        from .gamma_arithmetic import local_factorial_obstruction
        result=local_factorial_obstruction(args.n,args.numerator,args.denominator,args.d,args.prime,args.depth,work_limit=args.work_limit)
    elif args.command=='beta-period':
        from .gamma_arithmetic import beta_period
        result=beta_period(args.m)
    elif args.command=='finite-mellin':
        from .gamma_arithmetic import finite_mellin
        result=finite_mellin(args.indices,args.s)
    elif args.command=='witness-resolvent':
        from .witness_resolvent import subsequence_resolvent,verify_resolvent,resolvent_value
        result=subsequence_resolvent(args.matrix,args.seed,args.readouts,offset=args.offset,step=args.step)
        result['sampling']={'offset':args.offset,'step':args.step};result['index']=args.index
        result['output']=[resolvent_value(result,args.index,i) for i in range(len(args.readouts))]
        if args.verify:result['certificate_replay']=verify_resolvent(result)
    elif args.command=='connection-reweight':
        from .connection_polytope import ConnectionGraph
        from .connection_measure import ConnectionMeasure
        from .connection_updates import reweight,verify_reweight
        result=reweight(ConnectionMeasure(ConnectionGraph(args.vertices,tuple(args.edges),args.power),args.weights),args.new_weights)
        if args.verify:result['certificate_replay']=verify_reweight(result)
    elif args.command=='simplify-query':
        from .simplifier import simplify_query,verify_simplification,lift_model
        result=simplify_query(args.script,branch_limit=args.branch_limit)
        if args.model is not None:result['original_model']=lift_model(result,args.model)
        if args.verify:
            clean={k:v for k,v in result.items() if k!='original_model'}
            result['certificate_replay']=verify_simplification(clean)
    elif args.command=='analyze-power':
        from .simplifier import analyze_power,verify_analysis,answer_points
        result=analyze_power(args.coeff,args.d,interval=args.interval,work_limit=args.work_limit)
        if args.verify:result['certificate_replay']=verify_analysis(result,work_limit=args.work_limit)
        if args.question:result['question']=answer_points(result,args.question)
    elif args.command=='polynomial-pullback':
        from .simplifier import polynomial_pullback,verify_pullback
        result=polynomial_pullback(args.outer,args.inner,args.d,work_limit=args.work_limit)
        if args.verify:result['certificate_replay']=verify_pullback(result,work_limit=args.work_limit)
    elif args.command=='observable-machine':
        from .observable_machine import minimal_machine,verify_machine,word_output
        result=minimal_machine(args.operators,args.seed,args.readouts)
        result['output']=word_output(result,args.word,order=args.order)
        if args.verify:result['certificate_replay']=verify_machine(result)
    elif args.command=='recurrence-batch':
        from .observable_machine import recurrence_batch,verify_machine,power_outputs
        from .recurrence import Recurrence
        models=[Recurrence(tuple(Q(x) for x in m['coefficients']),tuple(Q(x) for x in m['initial'])) for m in args.models]
        result=recurrence_batch(models);result['index']=args.index;result['output']=power_outputs(result,args.index)
        if args.verify:result['certificate_replay']=verify_machine(result)
    elif args.command=='factored-scan':
        from .residue_cover import residue_cover
        from .factored_sieve import factored_cover,scan_factored,verify_factored_cover,DEFAULT_FACTORS
        cover=factored_cover(residue_cover(args.coeff,args.d),DEFAULT_FACTORS if args.factors is None else args.factors)
        result={'cover':cover,**scan_factored(cover,args.lo,args.hi,work_limit=args.work_limit,filter_limit=args.filter_limit),
            'scope':'complete integer solutions in the stated bounded interval; no global height claim'}
        if args.verify:result['certificate_replay']=verify_factored_cover(cover)
    elif args.command=='operator-algebra':
        from .operator_algebra import algebra_profile,verify_profile
        operators=[[[Q(x) if isinstance(x,str) else x for x in row] for row in a] for a in args.operators]
        result=algebra_profile(operators)
        if args.verify:result['certificate_replay']=verify_profile(result)
    elif args.command=='exact-solve':
        from .arithmetic_engine import ArithmeticEngine,verify_result
        result=ArithmeticEngine(work_limit=args.work_limit).solve(args.coeff,args.d)
        if args.verify:result['certificate_replay']=verify_result(result,work_limit=args.work_limit)
    elif args.command=='nearest-lift':
        from .closest_integer import IntegerLiftOptimizer,verify_optimum
        mass=None if args.mass is None else [[Q(x) if isinstance(x,str) else x for x in row] for row in args.mass]
        target=[Q(x) if isinstance(x,str) else x for x in args.target]
        result=IntegerLiftOptimizer(args.matrix,mass,node_limit=args.node_limit).nearest(args.rhs,target)
        if args.verify:result['certificate_replay']=verify_optimum(result,node_limit=args.node_limit)
    elif args.command=='integer-roots':
        from .sturm_fibres import root_certificate,verify_roots
        result=root_certificate(args.coeff,lo=args.lo,hi=args.hi,node_limit=args.node_limit)
        if args.verify:result['certificate_replay']=verify_roots(result,node_limit=args.node_limit)
    elif args.command=='square-fibres':
        from .sturm_fibres import square_fibres,verify_square_fibres
        result=square_fibres(args.coeff,args.k,work_limit=args.work_limit)
        if args.verify:result['certificate_replay']=verify_square_fibres(result,work_limit=args.work_limit)
    elif args.command=='connection-measure':
        from .connection_polytope import ConnectionGraph
        from .connection_measure import ConnectionMeasure,verify_measure,verify_conditioning
        measure=ConnectionMeasure(ConnectionGraph(args.vertices,tuple(args.edges),args.power),args.weights);result=measure.receipt()
        if measure.kernel is not None:result['conditioning']=measure.conditional(args.include,args.exclude)
        if args.verify:result['certificate_replay']=verify_measure(result) and ('conditioning' not in result or verify_conditioning(result,result['conditioning']))
    else:return False
    print(json.dumps(result,indent=2,default=exact_json));return True
