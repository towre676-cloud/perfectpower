"""CLI registration for recovered multiplicative arithmetic."""
import json
from fractions import Fraction
from pathlib import Path


def add_commands(sub):
    for name,description in [('monomial-solve','complete positive-integer multiplicative solving'),
                             ('monomial-rational','complete positive-rational multiplicative fibre'),
                             ('monomial-eliminate','exact elimination of variable exponents')]:
        p=sub.add_parser(name,help=description)
        p.add_argument('--matrix',type=json.loads,required=True)
        p.add_argument('--rhs',type=json.loads,help='JSON exact integers or fraction strings')
        if name=='monomial-eliminate':p.add_argument('--columns',type=json.loads,required=True)
        else:p.add_argument('--work-limit',type=int,default=1_000_000)
        if name=='monomial-solve':
            p.add_argument('--weights',type=json.loads)
            p.add_argument('--point-limit',type=int,default=100_000)
    sub.add_parser('monomial-recovery',help='recompute the August 2025 exponent and elimination packet')
    p=sub.add_parser('monomial-project',help='eliminate a finite positive monomial relation from a whole SMT query')
    p.add_argument('source',type=Path)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--point-limit',type=int,default=10000)


def dispatch(args):
    if not args.command.startswith('monomial-'):return False
    from .monomial import solve_monomial,solve_rational_monomial,eliminate_exponents,recovered_2025_packet
    if args.command=='monomial-recovery':out=recovered_2025_packet()
    elif args.command=='monomial-project':
        from .monomial_projection import project_monomial_query
        r=project_monomial_query(args.source.read_text(),point_limit=args.point_limit)
        args.output.write_text(r.smt)
        out={'eliminated':r.eliminated_symbols,'remaining':r.remaining_symbols,'points':r.points,
             'solution':r.solution,'linear':r.linear}
    else:
        if args.rhs is None:
            if args.command!='monomial-eliminate':raise ValueError('--rhs required for solving')
            rhs=None
        else:
            if any(type(x) not in (int,str) for x in args.rhs):raise ValueError('exact integer or fraction-string rhs required')
            rhs=[Fraction(x) for x in args.rhs]
        if args.command=='monomial-solve':out=solve_monomial(args.matrix,rhs,weights=args.weights,
                                                           work_limit=args.work_limit,point_limit=args.point_limit)
        elif args.command=='monomial-rational':out=solve_rational_monomial(args.matrix,rhs,work_limit=args.work_limit)
        else:out=eliminate_exponents(args.matrix,args.columns,rhs=rhs)
    print(json.dumps(out,indent=2));return True
