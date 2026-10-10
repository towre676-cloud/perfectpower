"""Unified JSON console for generating functions and exact budget queries."""
import json
from pathlib import Path
from .catalogue import encoded


def execute(request):
    if not isinstance(request, dict) or set(request)-{'kind', 'specification', 'query'} or not {'kind', 'specification'} <= set(request):
        raise ValueError('kind, specification and optional query required')
    kind, spec, query = request['kind'], request['specification'], request.get('query', {})
    if not isinstance(query, dict):
        raise ValueError('query must be an object')
    if kind == 'binomial_sum':
        from .telescoping import discover_binomial_sum, replay_binomial_sum, BinomialSumSequence
        packet = discover_binomial_sum(**spec)
        if packet.get('schema') != 'pp-binomial-telescoping/1':
            return {'definition': packet}
        sequence = BinomialSumSequence(packet)
        result = {'definition': packet, 'replay': replay_binomial_sum(packet)}
        if 'exponent' in query:
            result['power_window'] = sequence.power_hits(**query)
        else:
            result['terms'] = sequence.terms(**query)
        return result
    if kind == 'antidifference':
        from .telescoping import discover_antidifference, replay_antidifference, sum_from_antidifference
        packet = discover_antidifference(**spec)
        result = {'definition': packet}
        if packet.get('schema') == 'pp-antidifference/1':
            result['replay'] = replay_antidifference(packet)
            if query: result['finite_sum'] = sum_from_antidifference(packet, **query)
        elif query:
            raise ValueError('cannot sum an unresolved ansatz')
        return result
    if kind in ('rational', 'theta'):
        from .generating_functions import RationalSeries
        from .holonomic_series import ThetaSeries
        series = (RationalSeries if kind == 'rational' else ThetaSeries)(spec)
        return {'definition': series.evidence(), 'terms': series.terms(**query)}
    if kind == 'budget':
        from .budget_populations import BudgetPopulation
        if set(query)-{'budget', 'rank', 'point', 'start', 'size', 'modulus'} or 'budget' not in query:
            raise ValueError('budget query with optional rank, point, page or modulus required')
        pop = BudgetPopulation(spec); budget = query['budget']; modulus = query.get('modulus')
        result = {'definition': pop.evidence(), 'count': pop.count(budget, modulus),
                  'cumulative_count': pop.cumulative_count(budget, modulus)}
        if 'rank' in query:
            result['selected'] = pop.select(budget, query['rank'])
        if 'point' in query:
            result['rank'] = pop.rank(budget, query['point'])
        if 'size' in query or 'start' in query:
            result['page'] = pop.page(budget, query.get('start', 0), query.get('size', 20))
        return result
    if kind == 'semilinear':
        from .generating_functions import semilinear_series, RationalSeries
        packet = semilinear_series(spec)
        series = RationalSeries({k: packet['series'][k] for k in ('numerator', 'denominator')})
        return {'definition': packet, 'terms': series.terms(**query)}
    from .cost_resolvents import cost_resolvent, finite_machine_series, dynacomp_series, dynacomp_switched_series
    if kind == 'cost_machine':
        packet = cost_resolvent(spec)
    elif kind == 'finite_machine':
        packet = finite_machine_series(**spec)
    elif kind == 'dynacomp':
        if query:
            raise ValueError('DynaComp response export does not take a term query')
        return dynacomp_series(**spec)
    elif kind == 'dynacomp_switched':
        packet = dynacomp_switched_series(**spec)
    elif kind == 'wz':
        from .wz_certificates import discover_wz
        if query:
            raise ValueError('WZ search options belong in the specification')
        return discover_wz(**spec)
    else:
        raise ValueError('unsupported generating-function kind')
    from .generating_functions import RationalSeries
    if packet['schema'] == 'pp-finite-machine-series/1':
        out = packet['transport']['resolvent']['outputs']
    elif packet['schema'] == 'pp-cost-quotient/1':
        out = packet['resolvent']['outputs']
    else:
        out = packet['outputs']
    return {'definition': packet, 'terms': [RationalSeries({k: p[k] for k in ('numerator', 'denominator')}).terms(**query) for p in out]}


def add_commands(sub):
    p = sub.add_parser('generating-function', help='exact rational/theta series, budget populations and cost-machine exports')
    p.add_argument('specification', type=Path, help='JSON request with kind, specification, optional query')
    p.add_argument('--out', type=Path)


def cli(args):
    if args.command != 'generating-function':
        return False
    result = execute(json.loads(args.specification.read_text()))
    payload = encoded(result)+'\n'
    if args.out:
        args.out.write_text(payload)
    else:
        print(payload, end='')
    return True
