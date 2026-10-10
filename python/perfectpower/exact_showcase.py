"""A connected, reproducible example; constructed workloads, not industry data.

Population members are resource allocations, not ordered action histories.
The derived machine generates population counts at successive budgets.
"""
from fractions import Fraction as Q
from math import comb
from .budget_populations import BudgetPopulation
from .cost_resolvents import cost_quotient, verify_cost_quotient
from .generating import RationalGF, replay_generating
from .generating_functions import RationalSeries
from .binary64 import bits, power_certificate, dot_bits, exact
from .telescoping import discover_binomial_sum, BinomialSumSequence


def population_spec(filtered=False):
    if type(filtered) is not bool:
        raise ValueError('filtered must be Boolean')
    return {'coordinates': ([{'weight': 1, 'modulus': 3, 'residue': 1},
                             {'weight': 2, 'modulus': 5, 'residue': 2}]
                            if filtered else [{'weight': 1}, {'weight': 2}])}


def oracle(budget, filtered=False):
    """Independent elimination: admissible x lie on one arithmetic progression."""
    if type(budget) is not int or not 0 <= budget < 2**64:
        raise ValueError('nonnegative 64-bit budget required')
    population_spec(filtered)
    if filtered:
        # y=2+5t, x=budget-4-10t; x=1 mod 3 means t=budget-5 mod 3.
        ymax_start = 2 + 5*((budget-5) % 3)
        xmax = budget-2*ymax_start
        step = 30
    else:
        xmax, step = budget, 2
    if xmax < 0:
        return {'count': 0, 'first_x': None, 'last_x': None, 'step': step}
    xmin = xmax % step
    return {'count': (xmax-xmin)//step+1, 'first_x': xmin,
            'last_x': xmax, 'step': step}


def query(budget=10**12, rank=100_000_000_007, objective=(3, 5), filtered=False):
    reference = oracle(budget, filtered)
    if type(rank) is not int or not 0 <= rank < reference['count']:
        raise ValueError('rank outside the selected population')
    if (not isinstance(objective, (list, tuple)) or len(objective) != 2 or
            any(type(c) is not int or abs(c) > 10**6 for c in objective)):
        raise ValueError('two integer objective coefficients of magnitude at most 10^6 required')
    pop = BudgetPopulation(population_spec(filtered))
    count = pop.count(budget)
    point = pop.select(budget, rank)
    back = pop.rank(budget, point)
    x = reference['first_x']+reference['step']*rank
    expected = [x, (budget-x)//2]
    if (count, point, back) != (reference['count'], expected, rank):
        raise AssertionError('population differs from independent integer elimination')
    # On x+2y=B the objective is (2a-b)x/2+bB/2. Its slope decides
    # the maximizing endpoint; zero slope retains every member as a tie.
    slope = 2*objective[0]-objective[1]
    best_rank = count-1 if slope > 0 else 0
    best = pop.select(budget, best_rank)
    score = sum(a*b for a, b in zip(objective, best))
    return {'budget': str(budget), 'rank': str(rank), 'count': str(count),
            'point': list(map(str, point)), 'reverse_rank': str(back),
            'filtered': filtered, 'specification': pop.specification,
            'objective': list(objective), 'maximum': str(score),
            'maximizer': list(map(str, best)), 'maximizer_rank': str(best_rank),
            'maximizer_count': str(count if slope == 0 else 1),
            'optimization_scope': 'this two-coordinate linear budget family; sign of exact objective slope',
            'independent_check': 'integer elimination and arithmetic progression; no GF coefficient algorithm'}


def matvec(matrix, vector):
    return [sum(c*x for c, x in zip(row, vector)) for row in matrix]


def four_count(budget):
    """Independent count for weights (1,2,1,2), from a finite power sum."""
    if budget < 0:
        return 0
    m = budget//2
    return ((m+1)*(m+2)*(2*m+3)//6 if budget % 2 == 0 else
            (m+1)*(m+2)*(m+3)//3)


def four_rank(budget, point):
    """Independent lex rank by summing three explicit suffix counts."""
    x, y, u, v = point
    if min(point) < 0 or x+2*y+u+2*v != budget:
        raise ValueError('allocation outside four-coordinate budget')
    q = (budget-x)//2
    return four_count(budget)-four_count(budget-x)+y*(q+1)-y*(y-1)//2+u//2


def large_space():
    budget, rank = 10**12, 10**30
    pop = BudgetPopulation({'coordinates': [{'weight': w} for w in (1, 2, 1, 2)]})
    count, point = pop.count(budget), pop.select(budget, rank)
    if count != four_count(budget) or pop.rank(budget, point) != rank or four_rank(budget, point) != rank:
        raise AssertionError('four-coordinate population differs from independent power sums')
    return {'budget': str(budget), 'rank': str(rank), 'count': str(count),
            'point': list(map(str, point)), 'weights': [1, 2, 1, 2],
            'reverse_rank': str(rank), 'series': pop.suffix[0].summary(),
            'independent_check': 'closed finite-power-sum count and summed suffix-count rank'}


def machine():
    gf = RationalGF((1,), (1, -1, -1, 1))
    realization = gf.packet()
    a = [[int(Q(c)) for c in row] for row in realization['A']]
    seed = [int(Q(c)) for c in realization['initial']]
    # Hidden states receive the visible states and circulate internally.
    # They evolve, but cannot affect the protected count readout.
    j = [[0, 1, 0], [0, 0, 1], [1, 0, 0]]
    large = [row+[0]*3 for row in a]
    large += [[int(i == k) for k in range(3)]+j[i] for i in range(3)]
    encoder = [[int(i == k) for k in range(6)] for i in range(3)]
    source = {'operators': [{'cost': 1, 'matrix': large}], 'seed': seed+[0]*3,
              'readouts': [[1, 0, 0, 0, 0, 0]]}
    transport = cost_quotient(source, encoder, [{'cost': 1, 'matrix': a}], [[1, 0, 0]])
    if not verify_cost_quotient(transport) or not replay_generating(realization):
        raise AssertionError('machine identities failed')
    out = transport['resolvent']['outputs'][0]
    if RationalGF(out['numerator'], out['denominator']) != gf:
        raise AssertionError('transport output differs from population generating function')
    v, small = source['seed'], seed
    for n in range(257):
        if v[0] != small[0] or small[0] != n//2+1:
            raise AssertionError('independent matrix evolution differs from count formula')
        v, small = matvec(large, v), matvec(a, small)
    return {'source': source, 'transport': transport, 'minimal_realization': realization,
            'checked_prefix_length': 257,
            'meaning': 'output at time n is the number of allocations x+2y=n; not the number of ordered resource histories',
            'minimality_scope': 'exact nonsingular 3 by 3 response Hankel witness, replayed in Python; no new source-bound Lean packet'}


def build_results():
    main = query()
    restricted = query(rank=10_000_000_007, filtered=True)
    series = RationalSeries({'numerator': [1], 'denominator': [1, -1, -1, 1]})
    tail = series.analytic_tail('1/8', '1/4', 24)
    partial = sum(series.coefficient(n)*Q(1, 8)**n for n in range(24))
    value = Q(512, 441)
    if not partial <= value <= partial+Q(tail['absolute_tail_upper']):
        raise AssertionError('infinite rational sum escapes remainder bound')
    packet = discover_binomial_sum(2, max_order=2)
    seq = BinomialSumSequence(packet)
    values = seq.terms(size=64)
    if values != [Q(comb(2*n, n)) for n in range(64)]:
        raise AssertionError('telescoping sequence differs from independent central binomial formula')
    binary = {'stored_point_one': power_certificate(bits(0.1), 2),
              'stored_quarter': power_certificate(bits(0.25), 2),
              'sequential_cancellation': str((1e16+1.0)-1e16),
              'round_once_cancellation': str(exact(dot_bits([bits(1e16), bits(1.0), bits(-1e16)], [bits(1.0)]*3)))}
    return {'schema': 'pp-exact-space-showcase/1', 'population': main,
            'four_coordinate_population': large_space(),
            'restricted_population': restricted, 'machine': machine(),
            'analytic': {'tail': tail, 'partial_sum': str(partial), 'exact_sum': str(value),
                         'interval': [str(partial), str(partial+Q(tail['absolute_tail_upper']))]},
            'telescoping': {'definition': packet, 'prefix': list(map(str, values[:12])),
                            'independent_checked_terms': 64, 'power_window': seq.power_hits(size=64)},
            'binary': binary,
            'evidence': {'new_execution': 'exact Python calculations with independent algebraic checks',
                         'lean_foundations': 'receipts/series_kernel/validation.json',
                         'new_source_bound_lean_acceptance': False,
                         'benchmark_scope': 'constructed workloads on this machine; no industrial performance claim'}}
