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


def dispatch(args):
    if args.command=='exact-solve':
        from .arithmetic_engine import ArithmeticEngine,verify_result
        result=ArithmeticEngine(work_limit=args.work_limit).solve(args.coeff,args.d)
        if args.verify:result['certificate_replay']=verify_result(result,work_limit=args.work_limit)
    elif args.command=='nearest-lift':
        from .closest_integer import IntegerLiftOptimizer,verify_optimum
        mass=None if args.mass is None else [[Q(x) if isinstance(x,str) else x for x in row] for row in args.mass]
        target=[Q(x) if isinstance(x,str) else x for x in args.target]
        result=IntegerLiftOptimizer(args.matrix,mass,node_limit=args.node_limit).nearest(args.rhs,target)
        if args.verify:result['certificate_replay']=verify_optimum(result,node_limit=args.node_limit)
    else:return False
    print(json.dumps(result,indent=2,default=exact_json));return True
