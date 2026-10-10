"""Application-facing exact population and dataset commands."""
import json
from pathlib import Path
from .populations import ExactPopulation
from .population_algebra import PopulationComparison


def add_commands(sub):
    p = sub.add_parser('population', help='compile, count, rank/select and sample finite exact configuration populations')
    p.add_argument('--spec', type=Path, required=True, help='JSON domain, curve or species population specification')
    action = p.add_mutually_exclusive_group()
    action.add_argument('--rank', type=int, help='select zero-based global object rank')
    action.add_argument('--locate', type=json.loads, help='recover rank from {parameter:n}, {x:x,y:y}, or {exponents:[...]}')
    action.add_argument('--page', type=json.loads, help='materialize [start,size] rank window')
    action.add_argument('--sample', type=int, help='uniform sample size')
    action.add_argument('--objective', help='domain JSON coefficients, or polynomial curve expression')
    p.add_argument('--seed', type=int, default=0)
    p.add_argument('--replace', action='store_true')
    p.add_argument('--output', type=Path, help='JSONL dataset destination (requires --sample)')
    p.add_argument('--sense', choices=('min', 'max'), default='min')
    p.add_argument('--row-limit', type=int, default=100000)

    p = sub.add_parser('population-compare', help='exact Boolean subsets and shared-object address transport')
    p.add_argument('--spec', type=Path, required=True, help='JSON universe/left/right specification')
    action = p.add_mutually_exclusive_group()
    action.add_argument('--rank', type=int, help='select rank in --part')
    action.add_argument('--locate', type=json.loads, help='original parameter or coordinate object')
    action.add_argument('--page', type=json.loads, help='[start,size] in --part')
    action.add_argument('--sample', type=int)
    action.add_argument('--transport', type=json.loads, help='[source,rank,target]')
    p.add_argument('--part', default='universe', choices=PopulationComparison.PARTS)
    p.add_argument('--seed', type=int, default=0)
    p.add_argument('--row-limit', type=int, default=100000)


def dispatch(args):
    if args.command == 'population-compare':
        obj=PopulationComparison(json.loads(args.spec.read_text()),row_limit=args.row_limit)
        if args.rank is not None:answer=obj.select(args.part,args.rank)
        elif args.locate is not None:answer=obj.locate(**args.locate)
        elif args.page is not None:answer=obj.page(args.part,*args.page)
        elif args.sample is not None:answer=obj.sample(args.part,args.sample,seed=args.seed)
        elif args.transport is not None:answer=obj.transport(*args.transport)
        else:answer=obj.summary()
        print(json.dumps(answer,indent=2));return True
    if args.command != 'population':
        return False
    if args.output is not None and args.sample is None:
        raise ValueError('--output requires --sample')
    population = ExactPopulation(json.loads(args.spec.read_text()), row_limit=args.row_limit)
    if args.rank is not None:
        answer = population.select(args.rank)
    elif args.locate is not None:
        answer = population.locate(**args.locate)
    elif args.page is not None:
        answer = population.page(*args.page)
    elif args.sample is not None:
        answer = (population.export(args.output, size=args.sample, seed=args.seed, replace=args.replace)
                  if args.output is not None else population.sample(args.sample, seed=args.seed, replace=args.replace))
    elif args.objective is not None:
        objective = json.loads(args.objective) if population.specification['kind'] == 'domain' else args.objective
        answer = population.optimize(objective, sense=args.sense)
    else:
        answer = population.summary()
    print(json.dumps(answer, indent=2))
    return True
