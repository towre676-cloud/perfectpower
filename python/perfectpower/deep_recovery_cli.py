"""Console access to the four deep historical recoveries."""
import json
from fractions import Fraction
from .quotient_algebra import Element


def exact_json(value):
    if isinstance(value,Fraction):return str(value)
    if isinstance(value,Element):return list(map(str,value.coefficients))
    raise TypeError(f'cannot encode {type(value).__name__}')


def add_commands(sub):
    p=sub.add_parser('power-sums',help='complete sorted positive-box search for three or four powers')
    p.add_argument('--degree',type=int,required=True);p.add_argument('--terms',type=int,choices=(3,4),required=True)
    p.add_argument('--bound',type=int,required=True);p.add_argument('--work-limit',type=int,default=1_000_000)
    p.add_argument('--primitive',action='store_true')
    p=sub.add_parser('power-composition',help='complete integer lifting from a supported outer quartic')
    p.add_argument('--coeff',type=json.loads,required=True,help='JSON integer coefficients, low to high')
    p.add_argument('--power',type=int,required=True);p.add_argument('--work-limit',type=int,default=100_000)
    p=sub.add_parser('finite-weil',help='exact commutant of the recovered Fourier/chirp pair, level <= 9')
    p.add_argument('--level',type=int,required=True)
    p=sub.add_parser('weighted-hodge',help='finite exact Hodge projectors with supplied rational mass matrices')
    p.add_argument('--chain',type=json.loads,required=True,help='JSON with boundary1, boundary2, mass0, mass1, mass2')


def dispatch(args):
    if args.command=='power-sums':
        from .power_sums import search_power_sums
        result=search_power_sums(args.degree,args.terms,args.bound,work_limit=args.work_limit,primitive_only=args.primitive)
    elif args.command=='power-composition':
        from .polynomial_symmetry import solve_power_composition
        result=solve_power_composition(args.coeff,args.power,work_limit=args.work_limit)
    elif args.command=='finite-weil':
        from .finite_weil import commutant
        result=commutant(args.level)
    elif args.command=='weighted-hodge':
        from .weighted_hodge import weighted_hodge
        data=args.chain
        if set(data)!={'boundary1','boundary2','mass0','mass1','mass2'}:raise ValueError('exact chain and three mass matrices required')
        def entries(a):return [[Fraction(x) if isinstance(x,str) else x for x in row] for row in a]
        result=weighted_hodge(**{k:entries(v) for k,v in data.items()})
    else:return False
    print(json.dumps(result,indent=2,default=exact_json));return True
