"""Exact finite applications of monomial-box, CRT and restricted-digit machinery.

Counts refer to distinct objects. Work exhaustion returns no partial exact answer.
The published infinite theorems are motivation, not claims proved by this module.
"""
from functools import lru_cache
from itertools import combinations, product
from math import comb, gcd, prod
import json

from .divisor_square import WorkLimit


def integer(x, minimum=None):
    if type(x) is not int or minimum is not None and x < minimum:
        raise ValueError('integer outside the supported domain')
    return x


class MonomialPopulation:
    """Union of closed exponent boxes, optionally restricted to a total degree.

    Lexicographic rank/select uses bounded-composition inclusion-exclusion, so
    a huge population need not be enumerated or expanded into a histogram.
    """
    def __init__(self, generators, degree=None, work_limit=1_000_000):
        self.limit = integer(work_limit, 1)
        if not isinstance(generators, (list, tuple)) or not generators:
            raise ValueError('at least one maximal exponent vector required')
        n = len(generators[0])
        if not 1 <= n <= 12 or len(generators) > 8:
            raise ValueError('support is 1–12 variables and at most eight generators')
        vectors = []
        for g in generators:
            if len(g) != n:
                raise ValueError('equal dimensions required')
            vectors.append(tuple(integer(x, 0) for x in g))
        unique = sorted(set(vectors))
        self.generators = tuple(g for g in unique if not any(g != h and all(x <= y for x, y in zip(g, h)) for h in unique))
        self.n = n
        self.degree = None if degree is None else integer(degree, 0)
        self.work = 0
        terms = {}
        for length in range(1, len(self.generators) + 1):
            for subset in combinations(self.generators, length):
                box = tuple(map(min, zip(*subset)))
                terms[box] = terms.get(box, 0) + (-1) ** (length + 1)
        self.terms = tuple((g, s) for g, s in terms.items() if s)
        self.bounds = tuple(map(max, zip(*self.generators)))
        self.count = self._slice((), None)

    def _tick(self):
        self.work += 1
        if self.work > self.limit:
            raise WorkLimit('monomial inclusion-exclusion work limit; no complete query returned')

    @lru_cache(maxsize=4096)
    def _box(self, widths, degree):
        self._tick()
        if any(w < 0 for w in widths):
            return 0
        if degree is None:
            return prod(w + 1 for w in widths)
        if not widths:
            return int(degree == 0)
        if degree < 0 or degree > sum(widths):
            return 0
        n = len(widths)
        result = 0
        for mask in range(1 << n):
            self._tick()
            remainder = degree - sum(widths[i] + 1 for i in range(n) if mask >> i & 1)
            if remainder >= 0:
                result += (-1) ** mask.bit_count() * comb(remainder + n - 1, n - 1)
        return result

    def _slice(self, prefix, upper):
        result = 0
        for box, sign in self.terms:
            self._tick()
            if any(x > box[i] for i, x in enumerate(prefix)):
                continue
            widths = box[len(prefix):]
            if upper is not None and widths:
                widths = (min(widths[0], upper), *widths[1:])
            degree = None if self.degree is None else self.degree - sum(prefix)
            result += sign * self._box(widths, degree)
        return result

    def select(self, rank):
        rank = integer(rank, 0)
        if rank >= self.count:
            raise ValueError('rank outside population')
        prefix = ()
        for bound in self.bounds:
            lo, hi = 0, bound
            while lo < hi:
                mid = (lo + hi) // 2
                if self._slice(prefix, mid) > rank:
                    hi = mid
                else:
                    lo = mid + 1
            rank -= self._slice(prefix, lo - 1)
            prefix += (lo,)
        return list(prefix)

    def rank(self, vector):
        if len(vector) != self.n:
            raise ValueError('wrong vector dimension')
        vector = tuple(integer(x, 0) for x in vector)
        if not any(all(x <= y for x, y in zip(vector, g)) for g in self.generators) or self.degree is not None and sum(vector) != self.degree:
            raise ValueError('vector outside population')
        rank, prefix = 0, ()
        for x in vector:
            rank += self._slice(prefix, x - 1)
            prefix += (x,)
        return rank

    def histogram(self):
        # Separate counters keep degree-query caching and their budgets bounded.
        stop = max(map(sum, self.generators))
        if (stop + 1) * len(self.terms) * (1 << self.n) > self.limit:
            raise WorkLimit('histogram work limit; query individual degrees instead')
        values = []
        for degree in range(stop + 1):
            values.append(sum(sign * self._box(box, degree) for box, sign in self.terms))
        return values

    def packet(self, ranks=(), histogram=False):
        result = {'schema': 'pp-monomial-population/1', 'generators': self.generators,
                  'degree': self.degree, 'count': str(self.count),
                  'selected': [{'rank': str(r), 'vector': self.select(r)} for r in ranks],
                  'scope': 'Exact distinct exponent vectors in the supplied finite union of boxes.',
                  'pure': len(set(map(sum, self.generators))) == 1,
                  'work_limit': self.limit}
        if histogram:
            h = self.histogram()
            result['histogram'] = list(map(str, h))
            result['log_concavity_slacks'] = [str(h[i] ** 2 - h[i - 1] * h[i + 1]) for i in range(1, len(h) - 1)]
            result['log_concave'] = all(h[i] ** 2 >= h[i - 1] * h[i + 1] for i in range(1, len(h) - 1))
        result['work'] = self.work
        return result


def merge_residue(a, m, b, n):
    """General CRT, including consistent noncoprime moduli."""
    d = gcd(m, n)
    if (b - a) % d:
        return None
    q = n // d
    t = 0 if q == 1 else (b - a) // d * pow(m // d, -1, q) % q
    modulus = m * q
    return (a + m * t) % modulus, modulus


class ResiduePopulation:
    def __init__(self, lo, hi, constraints, work_limit=1_000_000):
        self.lo, self.hi = integer(lo), integer(hi)
        if hi < lo:
            raise ValueError('ordered inclusive interval required')
        self.limit = integer(work_limit, 1)
        self.work = 0
        states, modulus = {0}, 1
        for constraint in constraints:
            m = integer(constraint['modulus'], 1)
            allowed = {integer(x) % m for x in constraint['allowed']}
            new = set()
            if len(states) * len(allowed) + self.work > self.limit:
                raise WorkLimit('CRT state-product work limit; no count returned')
            new_modulus = modulus * m // gcd(modulus, m)
            for a, b in product(states, allowed):
                self.work += 1
                merged = merge_residue(a, modulus, b, m)
                if merged is not None:
                    new.add(merged[0])
            states, modulus = new, new_modulus
        self.residues, self.modulus = sorted(states), modulus
        self.count = self.before(hi)

    def before(self, hi):
        if hi < self.lo:
            return 0
        return sum((hi - a) // self.modulus - (self.lo - 1 - a) // self.modulus for a in self.residues)

    def select(self, rank):
        rank = integer(rank, 0)
        if rank >= self.count:
            raise ValueError('rank outside population')
        lo, hi = self.lo, self.hi
        while lo < hi:
            mid = (lo + hi) // 2
            if self.before(mid) > rank:
                hi = mid
            else:
                lo = mid + 1
        return lo

    def rank(self, value):
        value = integer(value)
        if not self.lo <= value <= self.hi or value % self.modulus not in self.residues:
            raise ValueError('integer outside population')
        return self.before(value - 1)

    def packet(self, ranks=()):
        return {'schema': 'pp-crt-population/1', 'interval': [self.lo, self.hi],
                'modulus': str(self.modulus), 'residues': list(map(str, self.residues)),
                'count': str(self.count), 'selected': [{'rank': str(r), 'value': str(self.select(r))} for r in ranks],
                'work': self.work, 'work_limit': self.limit,
                'scope': 'Exact distinct integers in the supplied finite inclusive interval.'}


def digit_values(base, digits, length, work_limit):
    base, length = integer(base, 2), integer(length, 0)
    if length > min(work_limit, 10000):
        raise WorkLimit('digit-place work limit')
    digits = sorted({integer(d, 0) for d in digits})
    if not digits or any(d >= base for d in digits):
        raise ValueError('nonempty base-valid digits required')
    if len(digits) ** length > work_limit:
        raise WorkLimit('digit population work limit')
    values = [0]
    place = 1
    for _ in range(length):
        values = [v + place * d for v in values for d in digits]
        place *= base
    return sorted(values)


def digit_sumset(spec, work_limit=1_000_000):
    work_limit = integer(work_limit, 1)
    a, b = spec['left'], spec['right']
    left = digit_values(a['base'], a['digits'], a['length'], work_limit)
    right = digit_values(b['base'], b['digits'], b['length'], work_limit)
    if len(left) * len(right) > work_limit:
        raise WorkLimit('sumset pair work limit; no exact answer returned')
    sums = {}
    for x, y in product(left, right):
        sums[x + y] = sums.get(x + y, 0) + 1
    stop = integer(spec.get('stop', max(sums) + 1), 1)
    population = sorted(x for x in sums if 0 <= x < stop)
    from fractions import Fraction
    return {'schema': 'pp-restricted-digit-sumset/1', 'input': spec,
            'interval': [0, stop], 'interval_convention': 'half-open',
            'count': str(len(population)), 'representation_count': str(sum(sums[x] for x in population)),
            'density': str(Fraction(len(population), stop)),
            'collision_excess': str(sum(sums[x] - 1 for x in population)),
            'values': population, 'work': len(left) * len(right), 'work_limit': work_limit,
            'scope': 'Exact finite digit lengths; finite densities do not prove an asymptotic density theorem.'}


def add_commands(sub):
    p = sub.add_parser('research-count', help='monomial degree counts, CRT populations and distinct restricted-digit sums')
    p.add_argument('operation', choices=['monomial', 'crt', 'digits'])
    p.add_argument('input', help='JSON model file')
    p.add_argument('--work-limit', type=int, default=1_000_000)
    p.add_argument('--output')


def cli(args):
    if args.command != 'research-count':
        return False
    from pathlib import Path
    spec = json.loads(Path(args.input).read_text())
    if args.operation == 'monomial':
        pop = MonomialPopulation(spec['generators'], spec.get('degree'), args.work_limit)
        result = pop.packet(spec.get('ranks', []), spec.get('histogram', False))
    elif args.operation == 'crt':
        pop = ResiduePopulation(spec['lo'], spec['hi'], spec['constraints'], args.work_limit)
        result = pop.packet(spec.get('ranks', []))
    else:
        result = digit_sumset(spec, args.work_limit)
    raw = json.dumps(result, indent=2) + '\n'
    if args.output:
        Path(args.output).write_text(raw)
    else:
        print(raw, end='')
    return True
