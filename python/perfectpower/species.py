"""Exact prime-exponent species and bounded structural populations.

A population contains exponent patterns, not every integer realizing a pattern.
Bounds concern the least representative. All decisions use integer arithmetic.
"""
from functools import reduce
from math import gcd, prod
from .divisor_square import Budget, WorkLimit


def natural(x, name, minimum=0):
    if type(x) is not int or x < minimum:
        raise ValueError(f'{name} must be an integer >= {minimum}')
    return x


def exponents(values):
    a = tuple(values)
    if len(a) > 128 or any(type(v) is not int or not 1 <= v <= 4096 for v in a):
        raise ValueError('at most 128 positive integer exponents <= 4096 required')
    if tuple(sorted(a, reverse=True)) != a:
        raise ValueError('exponents must be nonincreasing')
    return a


def _primes():
    known = []
    p = 2
    while True:
        if all(p % q for q in known if q*q <= p):
            known.append(p)
            yield p
        p += 1


def occupations(values):
    a = exponents(values)
    return tuple(v - (a[i+1] if i+1 < len(a) else 0) for i, v in enumerate(a))


def from_occupations(values):
    c = tuple(values)
    if len(c) > 128 or any(type(v) is not int or v < 0 for v in c):
        raise ValueError('at most 128 nonnegative integer occupations required')
    if c and not c[-1]:
        raise ValueError('remove trailing zero occupations')
    return exponents(tuple(sum(c[i:]) for i in range(len(c))))


def minimum(values):
    a = exponents(values)
    return prod(p**e for p, e in zip(_primes(), a))


def invariants(values):
    a = exponents(values)
    if sum(a) > 4096:
        raise WorkLimit('divisor rank polynomial degree exceeds 4096')
    budget = Budget(2_000_000)
    # Rank polynomial of the product of chains, exact coefficient convolution.
    rank_poly = [1]
    for e in a:
        nxt = [0]*(len(rank_poly)+e)
        for i, c in enumerate(rank_poly):
            for j in range(e+1):
                budget.spend()
                nxt[i+j] += c
        rank_poly = nxt
    power_gcd = reduce(gcd, a, 0)
    return {'exponents': list(a), 'occupations': list(occupations(a)),
            'least_representative': minimum(a), 'omega': sum(a),
            'distinct_prime_count': len(a), 'divisor_count': prod(e+1 for e in a),
            'divisor_rank_polynomial': rank_poly,
            'power_exponent_gcd': power_gcd,
            'power_exponents': [d for d in range(2, power_gcd+1) if power_gcd % d == 0],
            'unit_all_power_exponents': not a}


def power_divisor_count(values, degree):
    natural(degree, 'degree', 2)
    return prod(e//degree+1 for e in exponents(values))


def species_of(n, *, work_limit=1_000_000):
    """Trial-factor a positive integer within a declared work budget."""
    natural(n, 'n', 1)
    if n.bit_length() > 4096:
        raise WorkLimit('integer exceeds 4096 bits')
    budget = Budget(work_limit)
    factors = []
    p = 2
    while p*p <= n:
        budget.spend()
        if n % p == 0:
            e = 0
            while n % p == 0:
                budget.spend()
                n //= p
                e += 1
            factors.append(e)
        p = 3 if p == 2 else p+2
    if n > 1:
        factors.append(1)
    return exponents(sorted(factors, reverse=True))


class SpeciesPopulation:
    """Prefix-first ordered species with least representative <= bound.

    Optional filters require all exponents divisible by power, each exponent
    below power_free, and exact divisor-count/total-exponent targets. The unit
    is present precisely when it satisfies those filters. State exhaustion
    raises without publishing a partial count.
    """
    def __init__(self, bound, *, power=1, power_free=None, divisor_count=None,
                 omega=None, state_limit=200_000):
        natural(bound, 'bound', 1)
        if bound.bit_length() > 512:
            raise WorkLimit('species bound exceeds 512 bits')
        natural(power, 'power', 1)
        if power_free is not None:
            natural(power_free, 'power_free', 2)
        if divisor_count is not None:
            natural(divisor_count, 'divisor_count', 1)
        if omega is not None:
            natural(omega, 'omega')
        self._spec = dict(bound=bound, power=power, power_free=power_free,
                          divisor_count=divisor_count, omega=omega)
        self._budget = Budget(state_limit)
        self._cache = {}
        self._primes = []
        primorial = 1
        for p in _primes():
            if primorial > bound//p:
                break
            primorial *= p
            self._primes.append(p)
        cap = bound.bit_length()-1
        if power_free is not None:
            cap = min(cap, power_free-1)
        self._root = (0, cap, bound, divisor_count, omega)
        self._cardinality = self._count(self._root)

    @property
    def cardinality(self):
        return self._cardinality

    def count(self):
        return self.cardinality

    @staticmethod
    def _stop(state):
        return state[3] in (None, 1) and state[4] in (None, 0)

    def _branches(self, state):
        i, cap, bound, tau, omega = state
        if i >= len(self._primes):
            return
        p = self._primes[i]
        step = self._spec['power']
        value = p**step if step <= cap else bound+1
        factor = value
        for a in range(step, cap+1, step):
            if value > bound:
                break
            if (tau is None or tau % (a+1) == 0) and (omega is None or a <= omega):
                yield a, (i+1, a, bound//value,
                          None if tau is None else tau//(a+1),
                          None if omega is None else omega-a)
            # Capped multiplication avoids unnecessary enormous powers.
            if value > bound//factor:
                break
            value *= factor

    def _count(self, state):
        if state in self._cache:
            return self._cache[state]
        self._budget.spend()
        total = int(self._stop(state))
        for _, child in self._branches(state):
            total += self._count(child)
        self._cache[state] = total
        return total

    def select(self, rank):
        natural(rank, 'rank')
        if rank >= self.cardinality:
            raise IndexError('species rank outside population')
        state, prefix = self._root, []
        while True:
            if self._stop(state):
                if rank == 0:
                    return tuple(prefix)
                rank -= 1
            for a, child in self._branches(state):
                count = self._count(child)
                if rank < count:
                    prefix.append(a)
                    state = child
                    break
                rank -= count
            else:
                raise AssertionError('species selection exhausted a complete count')

    def rank(self, values):
        a = exponents(values)
        state, rank = self._root, 0
        for chosen in a:
            rank += int(self._stop(state))
            for exponent, child in self._branches(state):
                if exponent == chosen:
                    state = child
                    break
                if exponent < chosen:
                    rank += self._count(child)
            else:
                raise ValueError('species outside population')
        if not self._stop(state):
            raise ValueError('species fails population filters')
        return rank

    def page(self, start=0, size=20):
        natural(start, 'start'); natural(size, 'size')
        if size > 10_000:
            raise WorkLimit('page size exceeds 10000')
        return [self.select(i) for i in range(start, min(start+size, self.cardinality))]

    def packet(self):
        return {'schema': 'pp-species-population/1', 'specification': dict(self._spec),
                'cardinality': self.cardinality, 'states': len(self._cache),
                'ordering': 'prefix first, then increasing next exponent',
                'scope': 'exponent species whose least positive representative meets bound',
                'formal_verification': False}
