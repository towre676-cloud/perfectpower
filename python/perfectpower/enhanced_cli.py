"""Integrated structural solving and exact closest integer observations."""
import json
from fractions import Fraction as Q
from .deep_recovery_cli import exact_json


def add_commands(sub):
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
    if args.command=='operator-algebra':
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
