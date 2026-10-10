"""Console for structural species, exact inequalities and 2-torsion candidates."""
import json
from pathlib import Path
from .psg_polynomial import parse


def add_commands(sub):
    p = sub.add_parser('species', help='exact invariants of a positive integer or exponent species')
    choice = p.add_mutually_exclusive_group(required=True)
    choice.add_argument('--integer', type=int); choice.add_argument('--exponents', type=json.loads)
    p = sub.add_parser('species-population', help='count and rank size-bounded exponent patterns')
    p.add_argument('--bound', required=True, type=int)
    p.add_argument('--power', type=int, default=1); p.add_argument('--power-free', type=int)
    p.add_argument('--divisor-count', type=int); p.add_argument('--omega', type=int)
    p.add_argument('--ranks', type=json.loads, default=[]); p.add_argument('--rank', type=json.loads)
    p.add_argument('--state-limit', type=int, default=200_000)
    p = sub.add_parser('quadratic-minimum', help='global quadratic minimum with every affine minimizer')
    p.add_argument('--variables', required=True); p.add_argument('--objective', required=True)
    p = sub.add_parser('matrix-psd', help='exact singular-aware rational LDL certificate')
    p.add_argument('--matrix', type=json.loads, required=True)
    p = sub.add_parser('toeplitz-schur', help='exact real Toeplitz positivity and nested scalar increments')
    p.add_argument('--moments',type=json.loads,required=True)
    p = sub.add_parser('inequality-bound',help='compile supplied weighted squares into a constrained real lower bound')
    p.add_argument('--variables',required=True);p.add_argument('--objective',required=True)
    p.add_argument('--lower',default='0');p.add_argument('--inequalities',type=json.loads,default=[])
    p.add_argument('--equalities',type=json.loads,default=[])
    p.add_argument('--squares',type=json.loads,default=[])
    p.add_argument('--ideal',type=json.loads,default=[]);p.add_argument('--out',type=Path)
    p = sub.add_parser('linear-stability', help='synthesize and check rational Lyapunov metric')
    p.add_argument('--matrix', type=json.loads, required=True); p.add_argument('--alpha', default='0')
    p.add_argument('--metric', type=json.loads)
    p = sub.add_parser('two-torsion-descent', help='complete squareclass candidates with finite local exclusions')
    p.add_argument('--a', type=int, required=True); p.add_argument('--b', type=int, required=True)
    p.add_argument('--places', type=json.loads, default=[[2,3],[3,2],[5,1],[7,1]])
    p.add_argument('--work-limit', type=int, default=100_000)
    p.add_argument('--rank-bound', action='store_true', help='combine both isogenous candidate sets into a rational rank bound')
    p = sub.add_parser('inequality-check', help='replay an exact Gram, bound or Lyapunov JSON certificate')
    p.add_argument('source', type=Path)


def cli(args):
    from . import species as S
    from . import inequality_certificates as I
    if args.command == 'species':
        result = S.invariants(S.species_of(args.integer) if args.integer is not None else args.exponents)
    elif args.command == 'species-population':
        pop = S.SpeciesPopulation(args.bound, power=args.power, power_free=args.power_free,
            divisor_count=args.divisor_count, omega=args.omega, state_limit=args.state_limit)
        result = pop.packet()
        if len(args.ranks) > 10_000:
            raise ValueError('at most 10000 ranks required')
        result['selected'] = [S.invariants(pop.select(i)) for i in args.ranks]
        if args.rank is not None:
            result['rank'] = pop.rank(args.rank)
    elif args.command == 'quadratic-minimum':
        result = I.quadratic_minimum(parse(args.objective, tuple(args.variables.split(','))))
    elif args.command == 'matrix-psd':
        result = I.psd_certificate(args.matrix)
    elif args.command == 'toeplitz-schur':
        result = I.toeplitz_certificate(args.moments)
    elif args.command == 'inequality-bound':
        variables=tuple(args.variables.split(','))
        read=lambda expression:parse(expression,variables)
        result=I.lower_bound_certificate(read(args.objective),args.lower,
            inequalities=list(map(read,args.inequalities)),equalities=list(map(read,args.equalities)),
            terms=[(t.get('indices',[]),I.squares_certificate(list(map(read,t['polynomials'])),t.get('weights')))
                   for t in args.squares],ideal=[(t['index'],read(t['multiplier'])) for t in args.ideal])
    elif args.command == 'linear-stability':
        result = (I.synthesize_lyapunov(args.matrix, args.alpha) if args.metric is None
                  else I.lyapunov_certificate(args.matrix, args.metric, args.alpha))
    elif args.command == 'two-torsion-descent':
        from .descent_squareclasses import descent_candidates, two_isogeny_rank_bound
        function = two_isogeny_rank_bound if args.rank_bound else descent_candidates
        result = function(args.a, args.b, places=args.places, work_limit=args.work_limit)
    elif args.command == 'inequality-check':
        packet = json.loads(args.source.read_text())
        functions = {'pp-rational-psd/1': I.check_psd, 'pp-polynomial-gram/1': I.check_gram,
                     'pp-semialgebraic-bound/1': I.check_lower_bound, 'pp-linear-lyapunov/1': I.check_lyapunov,
                     'pp-real-toeplitz-schur/1':I.check_toeplitz}
        schema = packet.get('schema')
        if schema not in functions:
            raise ValueError('unsupported inequality certificate schema')
        functions[schema](packet)
        result = {'accepted': True, 'schema': schema, 'formal_verification': False}
    else:
        return False
    encoded=json.dumps(result,indent=2)+'\n'
    if getattr(args,'out',None):args.out.write_text(encoded)
    else:print(encoded,end='')
    return True
