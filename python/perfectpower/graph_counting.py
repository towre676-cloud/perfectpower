"""Exact finite factor counting by separator tables; no floating point or SAT oracle."""
from itertools import product, combinations
from copy import deepcopy
from .graph_structure import elimination_forest, check_decomposition
from .divisor_square import WorkLimit


def normalize(spec):
    domains = spec['domains']; factors = spec['factors']; n = len(domains)
    if any(not isinstance(d,list) or not d or any(type(x) is not int for x in d) or len(set(d)) != len(d) for d in domains):
        raise ValueError('nonempty distinct integer domains required')
    cleaned = []
    for f in factors:
        scope = f['scope']; values = f['values']
        if len(set(scope)) != len(scope) or any(type(v) is not int or not 0 <= v < n for v in scope):
            raise ValueError('invalid factor scope')
        size = 1
        for v in scope: size *= len(domains[v])
        if len(values) != size or any(type(x) is not int or x < 0 for x in values):
            raise ValueError('factor table must contain nonnegative integer weights')
        cleaned.append({'scope':list(scope),'values':list(values)})
    return {'domains':deepcopy(domains),'factors':cleaned}


def primal_edges(spec):
    return sorted({tuple(sorted(e)) for f in spec['factors'] for e in combinations(f['scope'],2)})


def _table(f, domains):
    return dict(zip(product(*(domains[v] for v in f['scope'])), f['values']))


def count_factors(spec, *, order=None, cell_limit=1_000_000, evidence=None):
    """Sum-product variable elimination. Budget counts visited bag assignments.

    Empty factors retain their multiplicity; isolated variables retain their domain size.
    The certificate contains actual separator tables and is bound to the source model.
    """
    spec = normalize(spec)
    if type(cell_limit) is not int or cell_limit < 1: raise ValueError('positive cell budget required')
    domains = spec['domains']; n = len(domains); edges = primal_edges(spec)
    decomposition = elimination_forest(n,edges,order)
    fs = [(f['scope'],_table(f,domains)) for f in spec['factors']]
    steps = []; cells = 0; peak = 0; cache = {}; hits = 0; stored = 0
    for v in decomposition['order']:
        selected = [(s,t) for s,t in fs if v in s]; fs = [(s,t) for s,t in fs if v not in s]
        scope = sorted({v} | {x for s,t in selected for x in s}); boundary = [x for x in scope if x != v]
        size = 1
        for x in scope: size *= len(domains[x])
        locations = [[scope.index(x) for x in s] for s,t in selected]
        boundary_indices = [scope.index(x) for x in boundary]
        key = (tuple(tuple(domains[x]) for x in scope), scope.index(v),
               tuple(sorted((tuple(ix),tuple(t.values())) for (s,t),ix in zip(selected,locations))))
        output_size = size // len(domains[v]); stored += output_size
        if stored > cell_limit: raise WorkLimit('separator storage budget exceeded; no count returned')
        if key in cache:
            out = dict(cache[key]); hits += 1
        else:
            if cells + size > cell_limit: raise WorkLimit('separator assignment budget exceeded; no count returned')
            cells += size; peak = max(peak,size)
            out = {a:0 for a in product(*(domains[x] for x in boundary))}
            for a in product(*(domains[x] for x in scope)):
                weight = 1
                for (s,t),ix in zip(selected,locations): weight *= t[tuple(a[i] for i in ix)]
                target = tuple(a[i] for i in boundary_indices); out[target] += weight
            cache[key] = tuple(out.items())
        fs.append((boundary,out))
        steps.append({'variable':v,'scope':boundary,'values':list(out.values())})
    count = 1
    for s,t in fs: count *= t[()]
    packet = {'schema':'pp-separator-count/1','source':spec,'decomposition':decomposition,
              'steps':steps,'count':count,'cells_visited':cells,'peak_bag_assignments':peak,
              'kernel_checked':False,'message_cache_hits':hits,'separator_cells_stored':stored}
    if evidence is not None:
        check_decomposition(n,edges,evidence['decomposition'])
        if packet != evidence: raise ValueError('count certificate does not replay against source')
    return packet


def check_count(spec, packet, *, cell_limit=1_000_000):
    count_factors(spec,order=packet['decomposition']['order'],cell_limit=cell_limit,evidence=packet)
    return True


def cnf_model(variables, clauses, *, cell_limit=1_000_000):
    if type(variables) is not int or variables < 0: raise ValueError('nonnegative variable count required')
    factors = []; cells = 0
    for clause in clauses:
        clause = tuple(clause)
        if any(type(l) is not int or not 1 <= abs(l) <= variables for l in clause):
            raise ValueError('nonzero DIMACS literal within declared carrier required')
        scope = sorted({abs(l)-1 for l in clause}); positions = {v:i for i,v in enumerate(scope)}
        cells += 2 ** len(scope)
        if cells > cell_limit: raise WorkLimit('CNF factor compilation budget exceeded')
        values = [int(any(bool(a[positions[abs(l)-1]]) == (l>0) for l in clause)) for a in product((0,1),repeat=len(scope))]
        factors.append({'scope':scope,'values':values})
    return {'domains':[[0,1] for _ in range(variables)],'factors':factors}


def count_cnf(variables, clauses, **options):
    return count_factors(cnf_model(variables,clauses,cell_limit=options.get('cell_limit',1_000_000)),**options)


def predicate_factor(domains, scope, predicate, *, cell_limit=100000):
    """Bridge exact arithmetic predicates to explicitly finite domains."""
    scope = list(scope)
    if len(set(scope)) != len(scope) or any(type(v) is not int or not 0 <= v < len(domains) for v in scope):
        raise ValueError('invalid predicate scope')
    size = 1
    for v in scope: size *= len(domains[v])
    if size > cell_limit: raise WorkLimit('predicate compilation budget exceeded')
    values = []
    for a in product(*(domains[v] for v in scope)):
        result = predicate(*a)
        if type(result) is not bool: raise ValueError('predicate must return an exact bool')
        values.append(int(result))
    return {'scope':scope,'values':values}


def condition_model(spec, fixed):
    source = normalize(spec); out = deepcopy(source)
    for v,x in fixed.items():
        if type(v) is not int or not 0 <= v < len(out['domains']) or type(x) is not int or x not in out['domains'][v]:
            raise ValueError('conditioning outside domain')
        out['domains'][v] = [x]
    for f,g in zip(source['factors'],out['factors']):
        table = _table(f,source['domains'])
        g['values'] = [table[a] for a in product(*(out['domains'][v] for v in g['scope']))]
    return out


condition = condition_model


def unrank(spec, rank, **options):
    """Lexicographic selection for indicator factors only, in declared domain order."""
    spec = normalize(spec)
    if any(x not in (0,1) for f in spec['factors'] for x in f['values']):
        raise ValueError('ranking requires indicator factors')
    total = count_factors(spec,**options)['count']
    if type(rank) is not int or not 0 <= rank < total: raise ValueError('rank outside solution population')
    fixed = {}
    for v,d in enumerate(spec['domains']):
        for x in d:
            trial = {**fixed,v:x}; block = count_factors(condition(spec,trial),**options)['count']
            if rank < block: fixed[v] = x; break
            rank -= block
    return [fixed[v] for v in range(len(spec['domains']))]


def rank_assignment(spec, assignment, **options):
    spec = normalize(spec)
    if len(assignment) != len(spec['domains']) or any(x not in (0,1) for f in spec['factors'] for x in f['values']):
        raise ValueError('indicator factors and complete assignment required')
    if count_factors(condition(spec,dict(enumerate(assignment))),**options)['count'] != 1:
        raise ValueError('assignment is not a solution')
    rank = 0; fixed = {}
    for v,(d,x) in enumerate(zip(spec['domains'],assignment)):
        for y in d[:d.index(x)]: rank += count_factors(condition(spec,{**fixed,v:y}),**options)['count']
        fixed[v] = x
    return rank


class GraphPopulation:
    """Queryable indicator-factor population, with lexicographic original assignments.

    Operation budgets apply to each elimination run; rank/select perform several runs.
    """
    def __init__(self, specification, *, cell_limit=1_000_000):
        self._spec = normalize(specification); self._options = {'cell_limit':cell_limit}
        if any(x not in (0,1) for f in self._spec['factors'] for x in f['values']):
            raise ValueError('population membership requires indicator factors')
        self._packet = count_factors(self._spec,**self._options)

    def count(self): return self._packet['count']
    def certificate(self): return deepcopy(self._packet)
    def select(self, rank): return unrank(self._spec,rank,**self._options)
    def rank(self, assignment): return rank_assignment(self._spec,assignment,**self._options)
    def restrict(self, fixed): return GraphPopulation(condition(self._spec,fixed),**self._options)
    def sample(self, rng=None):
        import random
        if self.count()==0: raise ValueError('cannot sample an empty population')
        return self.select((rng or random.SystemRandom()).randrange(self.count()))
    def marginal(self, variable):
        if type(variable) is not int or not 0 <= variable < len(self._spec['domains']): raise ValueError('invalid variable')
        return {x:count_factors(condition(self._spec,{variable:x}),**self._options)['count'] for x in self._spec['domains'][variable]}
