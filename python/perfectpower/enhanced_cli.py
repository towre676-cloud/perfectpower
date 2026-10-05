"""Integrated structural solving and exact closest integer observations."""
import json
from fractions import Fraction as Q
from .deep_recovery_cli import exact_json


def add_commands(sub):
    p=sub.add_parser('integral-machine',help='minimal integer state realization preserving future outputs and observation divisibility')
    p.add_argument('--operators',type=json.loads,required=True);p.add_argument('--seed',type=json.loads,required=True)
    p.add_argument('--readouts',type=json.loads,required=True);p.add_argument('--word',type=json.loads,default=[])
    p.add_argument('--order',choices=('execution','written'),default='execution');p.add_argument('--observations',type=json.loads)
    p.add_argument('--verify',action='store_true')
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

    p=sub.add_parser('operator-algebra',help='exact generated algebra, commutant and double-commutant certificates')
    p.add_argument('--operators',type=json.loads,required=True);p.add_argument('--verify',action='store_true')


def dispatch(args):
    if args.command=='integral-machine':
        from .integral_machine import integral_machine,integral_word_output,observation_fibre,verify_integral_machine
        result=integral_machine(args.operators,args.seed,args.readouts)
        result['output']=integral_word_output(result,args.word,order=args.order)
        if args.observations is not None:result['observation_fibre']=observation_fibre(result,args.observations)
        if args.verify:result['certificate_replay']=verify_integral_machine(result)
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
