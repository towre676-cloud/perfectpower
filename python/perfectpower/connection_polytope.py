"""Exact cyclic gain graphs, forest determinants and their Newton polytopes.

No numerical eigenvalues or total-positive Grassmannian assertion is used.
Cyclotomic coefficients are represented in Q[z]/Phi_d(z). Enumeration is
explicitly budgeted; minimum-cost full-rank bases use matroid greedy instead.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from math import comb, gcd
from . import polyalg as P
from .quotient_algebra import QuotientAlgebra


def exact(value):
    if type(value) not in (int, Q, str):
        raise ValueError('exact integer, Fraction or rational string required')
    return Q(value)


@lru_cache(None)
def cyclotomic(d):
    if type(d) is not int or not 1 <= d <= 64:
        raise ValueError('cyclotomic order must be 1 through 64')
    f = P.poly([-1] + [0] * (d - 1) + [1])
    for k in range(1, d):
        if d % k == 0:
            f = P.exact_div(f, cyclotomic(k))
    return f


def algebra_determinant(rows, field):
    n = len(rows)
    if any(len(row) != n for row in rows):
        raise ValueError('square matrix required')
    a = [[field.element(x) for x in row] for row in rows]
    out, zero = field.element(1), field.element(0)
    for j in range(n):
        pivot = next((i for i in range(j, n) if a[i][j] != zero), None)
        if pivot is None:
            return zero
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            out = -out
        v = a[j][j]
        out = out * v
        inv = v.inverse()
        for i in range(j + 1, n):
            ratio = a[i][j] * inv
            for k in range(j + 1, n):
                a[i][k] = a[i][k] - ratio * a[j][k]
            a[i][j] = zero
    return out


def root_channel_graph(multiplicities, d):
    """Parallel paths whose adjacent loops enclose one labelled root each.

    Voltages are cumulative, so a loop across several faces detects the sum
    of their root multiplicities. This is a finite topological transport model.
    """
    xs = tuple(multiplicities)
    if any(type(r) is not int or r < 1 for r in xs):
        raise ValueError('positive integer root multiplicities required')
    voltages, total = [0], 0
    for r in xs:
        total += r
        voltages.append(total)
    return ConnectionGraph(2, tuple((0, 1, r) for r in voltages), d)


@dataclass(frozen=True)
class ConnectionGraph:
    vertices: int
    edges: tuple  # (source, target, voltage mod d); loops and parallel edges allowed
    power: int

    def __post_init__(self):
        if type(self.vertices) is not int or not 1 <= self.vertices <= 64:
            raise ValueError('vertices must be 1 through 64')
        if type(self.power) is not int or not 2 <= self.power <= 64:
            raise ValueError('power must be 2 through 64')
        edges = []
        for edge in self.edges:
            if len(edge) != 3 or any(type(x) is not int for x in edge):
                raise ValueError('edges require three integers')
            a, b, r = edge
            if not 0 <= a < self.vertices or not 0 <= b < self.vertices:
                raise ValueError('edge endpoint outside graph')
            edges.append((a, b, r % self.power))
        object.__setattr__(self, 'edges', tuple(edges))

    @property
    def field(self):
        return QuotientAlgebra(cyclotomic(self.power))

    def conjugate(self, element):
        field = self.field
        zinv = field.element([0, 1]) ** (self.power - 1)
        out = field.element(0)
        for coefficient in reversed(element.coefficients):
            out = out * zinv + coefficient
        return out

    def support(self, indices=None, character=1):
        """Rank certificate from tree potentials and cyclic residual labels."""
        if type(character) is not int:
            raise ValueError('integer character required')
        indices = tuple(range(len(self.edges))) if indices is None else tuple(indices)
        if len(set(indices)) != len(indices) or any(type(i) is not int or not 0 <= i < len(self.edges) for i in indices):
            raise ValueError('distinct valid edge indices required')
        adjacency = [[] for _ in range(self.vertices)]
        for i in indices:
            a, b, r = self.edges[i]
            adjacency[a].append((b, r * character, i))
            adjacency[b].append((a, -r * character, i))
        potentials = [None] * self.vertices
        components = []
        for start in range(self.vertices):
            if potentials[start] is not None:
                continue
            potentials[start] = 0
            queue, tree = [start], []
            for a in queue:
                for b, r, i in adjacency[a]:
                    if potentials[b] is None:
                        potentials[b] = (potentials[a] + r) % self.power
                        queue.append(b)
                        tree.append(i)
            nodes = set(queue)
            es = [i for i in indices if self.edges[i][0] in nodes]
            residuals = [(potentials[a] + character * r - potentials[b]) % self.power
                         for i in es for a, b, r in [self.edges[i]]]
            divisor = self.power
            for r in residuals:
                divisor = gcd(divisor, r)
            components.append({'vertices': queue, 'edges': es, 'tree_edges': tree,
                               'cycle_residuals': residuals,
                               'balanced': all(r == 0 for r in residuals),
                               'lift_components': divisor})
        nullity = sum(c['balanced'] for c in components)
        return {'components': components, 'potentials': potentials,
                'kernel_dimension': nullity, 'rank': self.vertices - nullity,
                'lift_components': sum(c['lift_components'] for c in components)}

    def incidence(self):
        field = self.field
        zeta = field.element([0, 1])
        rows = []
        for a, b, r in self.edges:
            row = [field.element(0) for _ in range(self.vertices)]
            row[a] = row[a] - zeta ** r
            row[b] = row[b] + 1
            rows.append(row)
        return rows

    def laplacian(self, weights=None):
        weights = self.weights(weights)
        field = self.field
        out = [[field.element(0) for _ in range(self.vertices)] for _ in range(self.vertices)]
        for row, w in zip(self.incidence(), weights):
            for i, x in enumerate(row):
                if x == field.element(0):
                    continue
                for j, y in enumerate(row):
                    out[i][j] = out[i][j] + self.conjugate(x) * y * w
        return out

    def weights(self, weights):
        values = (Q(1),) * len(self.edges) if weights is None else tuple(map(exact, weights))
        if len(values) != len(self.edges) or any(w < 0 for w in values):
            raise ValueError('one nonnegative rational weight per edge required')
        return values

    def forest_coefficient(self, indices):
        """Independent Kenyon product for a candidate n-edge forest."""
        field, out = self.field, self.field.element(1)
        zeta = field.element([0, 1])
        for c in self.support(indices)['components']:
            if len(c['edges']) != len(c['vertices']) or c['balanced']:
                return field.element(0)
            residuals = [r for r in c['cycle_residuals'] if r]
            if len(residuals) != 1:
                raise AssertionError('unicyclic tree certificate has wrong cycle count')
            h = zeta ** residuals[0]
            out = out * (field.element(2) - h - self.conjugate(h))
        return out

    def terms(self, subset_limit=100_000):
        m, n = len(self.edges), self.vertices
        if type(subset_limit) is not int or subset_limit < 1:
            raise ValueError('positive subset budget required')
        if n > 12 or comb(m, n) > subset_limit:
            raise ValueError('basis enumeration budget exceeded; use minimum_cost_basis')
        rows, field = self.incidence(), self.field
        terms = []
        for indices in combinations(range(m), n):
            coefficient = self.forest_coefficient(indices)
            minor = algebra_determinant([rows[i] for i in indices], field)
            if coefficient != minor * self.conjugate(minor):
                raise AssertionError('forest product disagrees with squared minor')
            if coefficient != field.element(0):
                terms.append((indices, coefficient))
        return terms

    def minimum_cost_basis(self, costs):
        costs = tuple(map(exact, costs))
        if len(costs) != len(self.edges) or any(c < 0 for c in costs):
            raise ValueError('one nonnegative exact cost per edge required')
        selected, steps = [], []
        current = 0
        for i in sorted(range(len(costs)), key=lambda j: (costs[j], j)):
            new_rank = self.support(selected + [i])['rank']
            if new_rank > current:
                selected.append(i)
                current = new_rank
                steps.append({'edge': i, 'rank': current, 'cost': str(costs[i])})
        full = current == self.vertices
        return {'status': 'FULL_RANK_BASIS' if full else 'RANK_DEFICIENT',
                'edges': selected, 'rank': current,
                'cost': str(sum((costs[i] for i in selected), Q(0))),
                'steps': steps, 'optimality_basis': 'linear-matroid greedy theorem',
                'formalized': False}

    def packet(self, weights=None, subset_limit=100_000):
        weights = self.weights(weights)
        terms, field = self.terms(subset_limit), self.field
        total = field.element(0)
        contributions = []
        for indices, coefficient in terms:
            value = coefficient
            for i in indices:
                value = value * weights[i]
            total = total + value
            contributions.append((indices, value))
        determinant = algebra_determinant(self.laplacian(weights), field)
        if total != determinant:
            raise AssertionError('Cauchy-Binet determinant replay failed')
        marginals = None
        if total != field.element(0):
            marginals = []
            inv = total.inverse()
            for i in range(len(self.edges)):
                p = field.element(0)
                for indices, value in contributions:
                    if i in indices:
                        p = p + value
                marginals.append(p * inv)
            if sum(marginals, field.element(0)) != field.element(self.vertices):
                raise AssertionError('basis marginal dimension failed')
        encode = lambda z: list(map(str, z.coefficients))
        return {'schema': 'pp-connection-polytope/1', 'power': self.power,
                'vertices': self.vertices, 'edges': [list(e) for e in self.edges],
                'cyclotomic_modulus': list(map(str, field.modulus)),
                'weights': list(map(str, weights)), 'determinant': encode(total),
                'terms': [{'edges': list(xs), 'coefficient': encode(c),
                           'exponent': [int(i in xs) for i in range(len(self.edges))]}
                          for xs, c in terms],
                'basis_count': len(terms),
                'essential_edges': [i for i in range(len(self.edges)) if terms and all(i in xs for xs, c in terms)],
                'edge_marginals': None if marginals is None else [encode(p) for p in marginals],
                'positive_support': self.support([i for i, w in enumerate(weights) if w]),
                'character_kernel_dimensions': [self.support(character=k)['kernel_dimension'] for k in range(self.power)],
                'checked_identities': ['squared minors = forest products', 'determinant = basis sum'],
                'formalized': False,
                'scope': 'exact cyclic connection; Newton polytope, not a claimed amplituhedron'}
