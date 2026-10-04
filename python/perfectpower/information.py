"""Target-conditioned information plans over explicitly finite arithmetic domains.

Exact Python, not verified execution. A finite domain is never an exponent bound.
Observations must be deterministic and hashable; they are evaluated once.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from collections import Counter


class PlanningLimit(ValueError):
    """The exhaustive optimality search did not finish; no optimum is returned."""


@dataclass(frozen=True)
class Observation:
    name: str
    read: object
    cost: int = 1

    def __post_init__(self):
        if not self.name or type(self.cost) is not int or self.cost < 0:
            raise ValueError('observation needs a name and nonnegative integer cost')
        if not callable(self.read):
            raise ValueError('observation readout must be callable')


class InformationProblem:
    """Find sufficient observations for a target, not for full reconstruction."""
    def __init__(self, states, target, observations, *, scope, premises=(),
                 pair_limit=1_000_000):
        self.states = tuple(states)
        if not isinstance(scope, str) or not scope.strip():
            raise ValueError('an explicit finite-domain scope is required')
        if len(set(self.states)) != len(self.states):
            raise ValueError('states must be distinct and hashable')
        self.observations = tuple(observations)
        names = [o.name for o in self.observations]
        if len(set(names)) != len(names):
            raise ValueError('observation names must be distinct')
        if type(pair_limit) is not int or pair_limit < 1:
            raise ValueError('positive pair budget required')
        if len(self.states)*(len(self.states)-1)//2 > pair_limit:
            raise PlanningLimit('pair budget exceeded')
        self.scope, self.premises = scope, tuple(premises)
        self.labels = tuple(target(s) for s in self.states)
        self.values = tuple(tuple(o.read(s) for s in self.states)
                            for o in self.observations)
        for label in self.labels:
            hash(label)
        for row in self.values:
            for value in row:
                hash(value)
        self.pairs = tuple((i,j) for i,j in combinations(range(len(self.states)),2)
                           if self.labels[i] != self.labels[j])
        self.masks = tuple(sum(1 << k for k,(i,j) in enumerate(self.pairs)
                               if row[i] != row[j]) for row in self.values)

    def _indices(self, names):
        names = tuple(names)
        if len(set(names)) != len(names):
            raise ValueError('repeated observation')
        lookup = {o.name:i for i,o in enumerate(self.observations)}
        if any(n not in lookup for n in names):
            raise ValueError('unknown observation')
        return tuple(lookup[n] for n in names)

    def ambiguity(self, names=()):
        indices = self._indices(names)
        for i,j in self.pairs:
            if all(self.values[k][i] == self.values[k][j] for k in indices):
                return {'left':self.states[i], 'right':self.states[j],
                        'left_target':self.labels[i], 'right_target':self.labels[j],
                        'shared_readout':tuple(self.values[k][i] for k in indices),
                        'separators':[o.name for k,o in enumerate(self.observations)
                                      if self.values[k][i] != self.values[k][j]]}
        return None

    def compile(self, existing=(), *, subset_limit=1_000_000):
        """Exhaustive weighted set cover of ALL disagreeing pairs, with decoder.

        Costs are additive exact integers. Existing observations are sunk costs.
        Ties use fewer added observations, then declaration order. A work-limit
        exception carries no false optimality claim.
        """
        existing = tuple(existing)
        fixed = self._indices(existing)
        if type(subset_limit) is not int or subset_limit < 1:
            raise ValueError('positive subset budget required')
        full = (1 << len(self.pairs))-1
        covered = 0
        for i in fixed:
            covered |= self.masks[i]
        available = (() if covered == full else
                     tuple(i for i in range(len(self.observations)) if i not in fixed))
        all_covered = covered
        for i in available:
            all_covered |= self.masks[i]
        base = {'scope':self.scope, 'premises':list(self.premises),
                'execution_verified':False, 'states':len(self.states),
                'disagreeing_pairs':len(self.pairs), 'existing':list(existing)}
        if all_covered != full:
            return {**base, 'status':'UNSEPARABLE',
                    'ambiguity':self.ambiguity(o.name for o in self.observations)}
        best, trials = None, 0
        for size in range(len(available)+1):
            for chosen in combinations(available,size):
                trials += 1
                if trials > subset_limit:
                    raise PlanningLimit('subset budget exceeded; optimum not established')
                score = (sum(self.observations[i].cost for i in chosen),size,chosen)
                if best is not None and score >= best[0]:
                    continue
                mask = covered
                for i in chosen:
                    mask |= self.masks[i]
                if mask == full:
                    best = score, chosen
        chosen = fixed + best[1]
        decoder = {}
        for j,label in enumerate(self.labels):
            key = tuple(self.values[i][j] for i in chosen)
            if key in decoder and decoder[key] != label:
                raise AssertionError('insufficient decoder')
            decoder[key] = label
        return {**base, 'status':'SUFFICIENT_ON_FINITE_DOMAIN', 'optimal':True,
                'added':[self.observations[i].name for i in best[1]],
                'cost':best[0][0], 'subsets_tested':trials,
                'decoder':[{'readout':key,'target':value} for key,value in decoder.items()]}


@dataclass(frozen=True)
class AffineTransport:
    """Diagonal rational affine map with exact, integral inverse restrictions."""
    scales: tuple
    shifts: tuple

    def __post_init__(self):
        scales, shifts = tuple(map(Fraction,self.scales)), tuple(map(Fraction,self.shifts))
        if not scales or len(scales) != len(shifts) or any(s == 0 for s in scales):
            raise ValueError('matching nonempty coordinates and nonzero scales required')
        object.__setattr__(self,'scales',scales)
        object.__setattr__(self,'shifts',shifts)

    def forward(self, point):
        if len(point) != len(self.scales):
            raise ValueError('coordinate dimension mismatch')
        return tuple(a*Fraction(x)+b for a,b,x in zip(self.scales,self.shifts,point))

    def pullback(self, point):
        if len(point) != len(self.scales):
            raise ValueError('coordinate dimension mismatch')
        xs = tuple((Fraction(y)-b)/a for a,b,y in zip(self.scales,self.shifts,point))
        return tuple(int(x) for x in xs) if all(x.denominator == 1 for x in xs) else None

    def then(self, after):
        """after ∘ self: execution order is explicit."""
        if len(self.scales) != len(after.scales):
            raise ValueError('coordinate dimension mismatch')
        return AffineTransport(tuple(b*a for a,b in zip(self.scales,after.scales)),
                               tuple(a*b+c for a,b,c in zip(after.scales,self.shifts,after.shifts)))

    def pullback_chain(self, point, after):
        """Require integral intermediate AND source coordinates; composition alone cannot."""
        middle = after.pullback(point)
        return None if middle is None else self.pullback(middle)


def push_counts(counts, mapping):
    out = Counter()
    for point, count in counts.items():
        out[mapping(point)] += count
    return dict(out)


def transport_defect(source, target, mapping):
    """Δ_f = f# source − target, as a finite signed multiplicity measure.

    Therefore Δ_(g∘f) = g# Δ_f + Δ_g for a specified intermediate measure.
    Counts are retained; no injectivity assumption or deduplication is used.
    """
    if any(type(n) is not int or n < 0 for measure in (source,target) for n in measure.values()):
        raise ValueError('input multiplicities must be nonnegative integers')
    pushed = push_counts(source,mapping)
    return {x:pushed.get(x,0)-target.get(x,0) for x in pushed.keys() | target.keys()
            if pushed.get(x,0) != target.get(x,0)}


def compile_square_query(coefficients, k, predicate, **budgets):
    """Consume existing exact charts, retaining unresolved fibre obligations."""
    from .divisor_square import analyse
    chart = analyse(coefficients,k,**budgets)
    witnesses = [p for p in chart['known_points'] if predicate(p)]
    status = 'SAT' if witnesses else 'UNSAT' if chart['complete'] else 'UNRESOLVED'
    return {'status':status, 'witnesses':witnesses,
            'complete_relation':chart['complete'],
            'residual_parameters':chart['residual_parameters'],
            'execution_verified':False, 'chart_contract':chart['contract']}


def polynomial_information(coefficients, degree, lo, hi, moduli, *, pair_limit=1_000_000):
    """Compile residues sufficient to decide exact power membership in [lo,hi).

    This is target decoding on this interval, NOT a global congruence obstruction.
    """
    from .divisor_square import evaluate
    from .core import integer_power_root
    if any(type(v) is not int for v in (degree,lo,hi)) or degree < 2 or hi < lo:
        raise ValueError('integer bounds and degree at least two required')
    coefficients, moduli = tuple(coefficients), tuple(moduli)
    if not coefficients or any(type(c) is not int for c in coefficients):
        raise ValueError('integer polynomial coefficients required')
    if any(type(m) is not int or m < 2 for m in moduli):
        raise ValueError('integer moduli at least two required')
    return InformationProblem(range(lo,hi),
        lambda n:integer_power_root(evaluate(coefficients,n),degree) is not None,
        [Observation(f'mod_{m}',lambda n,m=m:n % m) for m in moduli],
        scope=f'integer interval [{lo}, {hi}); degree={degree}; coefficients={coefficients}',
        pair_limit=pair_limit)
