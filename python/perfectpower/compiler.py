"""Structural arithmetic constraint compiler.

A program meets a constraint on a positive integer n:

  * PowerConstraint(F, d)                 F(n) = m^d for some integer m
  * QuadraticRootConstraint(a, b, c, F)   a y^2 + b y + c = F(n) for some integer y in a domain
  * TriangularConstraint(F)               y (y + 1) / 2 = F(n) for some integer y in a domain

compile_constraint() turns it into a Plan: a chain of exact reductions to a power constraint
(each with its forward map, its backward map and the admissibility conditions of the way back),
followed by a structural solver chosen from the atlas classification of the reduced problem.

The Plan states exactly one outcome:

  COMPLETE_FINITE           a complete finite list of solutions
  STRUCTURED_INFINITE       infinitely many solutions, generated exactly (every n, radical
                            parametrization, or Pell orbits)
  STRUCTURED_FILTERED       an exact generator of a reduced family followed by an exact
                            admissibility filter; iteration and counting to any N are exact, but
                            whether infinitely many survive the filter is not decided
  CLASSIFIED_FINITE         finitely many solutions (Siegel via Theorem G), no complete list;
                            iteration may still be exact to any given N (exact_to_any_N)
  NOT_ENUMERATED            finitely many solutions (Siegel via Theorem G) and no effective
                            enumeration here; only bounded_evidence(N), labelled as such

and separately where its justification comes from: Lean theorem names, pp-cert/1 certificates
checked in Lean, or the Python structural algorithm (tested against scans, not formally
verified).  execution_verified is always False: the Python that executes a plan is not itself
formally verified, whatever the status of the mathematics behind it.

A finiteness theorem never becomes an empty list: NOT_ENUMERATED plans refuse iter_hits.
"""
from __future__ import annotations

import json
import re
from fractions import Fraction
from math import log, sqrt
from dataclasses import dataclass, field
from math import isqrt
from pathlib import Path
from typing import Callable, Iterator

from .atlas import (_positive_orbits, _radical_param_hits, _positive_zeros,
                    classify, quadratic_square_hits, structural_count, structural_hits)
from .arith import is_square, pell_fundamental
from .core import integer_power_root

ROOT = Path(__file__).resolve().parents[2]

COMPLETE_FINITE = 'COMPLETE_FINITE'
STRUCTURED_INFINITE = 'STRUCTURED_INFINITE'
STRUCTURED_FILTERED = 'STRUCTURED_FILTERED'
CLASSIFIED_FINITE = 'CLASSIFIED_FINITE'
NOT_ENUMERATED = 'NOT_ENUMERATED'
BOUNDED_EVIDENCE = 'BOUNDED_EVIDENCE'

DOMAINS = {'int': lambda y: True, 'nonneg': lambda y: y >= 0, 'pos': lambda y: y >= 1}


class NotEnumerable(Exception):
    """The plan knows the solution set is finite but cannot list it."""


# ---------------------------------------------------------------------------
# polynomials (integer coefficients, low to high)
# ---------------------------------------------------------------------------

def _trim(f) -> tuple[int, ...]:
    f = [int(c) for c in f]
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return tuple(f) if f else (0,)


def peval(f, n: int) -> int:
    v = 0
    for c in reversed(f):
        v = v * n + c
    return v


def padd(f, g):
    k = max(len(f), len(g))
    return _trim([(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0) for i in range(k)])


def pscale(f, c: int):
    return _trim([c * x for x in f])


def pmul(f, g):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return _trim(out)


def ppow(f, e: int):
    out = (1,)
    for _ in range(e):
        out = pmul(out, f)
    return out


def pshow(f, var: str = 'n') -> str:
    terms = []
    for i in range(len(f) - 1, -1, -1):
        c = f[i]
        if c == 0:
            continue
        mono = '' if i == 0 else (var if i == 1 else f'{var}^{i}')
        if mono and abs(c) == 1:
            s = mono
        else:
            s = f'{abs(c)}' + (f'*{mono}' if mono else '')
        terms.append(('-' if c < 0 else '+', s))
    if not terms:
        return '0'
    head = ('-' if terms[0][0] == '-' else '') + terms[0][1]
    return head + ''.join(f' {sg} {s}' for sg, s in terms[1:])


# ---------------------------------------------------------------------------
# constraints
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class PowerConstraint:
    F: tuple[int, ...]
    d: int

    def describe(self) -> str:
        return f'{pshow(self.F)} = m^{self.d},  n >= 1, m in Z'

    def witnesses(self, n: int) -> list[int]:
        """All integer m with F(n) = m^d (the ground truth, by direct evaluation)."""
        return _power_witnesses(peval(self.F, n), self.d)


@dataclass(frozen=True)
class QuadraticRootConstraint:
    a: int
    b: int
    c: int
    F: tuple[int, ...]
    y_domain: str = 'int'

    def describe(self) -> str:
        return (f'{self.a}*y^2 + {self.b}*y + {self.c} = {pshow(self.F)},  n >= 1, '
                f'y in {_domain_text(self.y_domain)}')

    def witnesses(self, n: int) -> list[int]:
        return _quadratic_roots(self.a, self.b, self.c - peval(self.F, n), self.y_domain)


@dataclass(frozen=True)
class TriangularConstraint:
    F: tuple[int, ...]
    y_domain: str = 'nonneg'

    def describe(self) -> str:
        return f'y*(y+1)/2 = {pshow(self.F)},  n >= 1, y in {_domain_text(self.y_domain)}'

    def witnesses(self, n: int) -> list[int]:
        return _quadratic_roots(1, 1, -2 * peval(self.F, n), self.y_domain)


def _domain_text(dom: str) -> str:
    return {'int': 'Z', 'nonneg': 'Z>=0', 'pos': 'Z>=1'}[dom]


def _power_witnesses(v: int, d: int) -> list[int]:
    r = integer_power_root(v, d)
    if r is None:
        return []
    if d % 2 == 0 and r != 0:
        return sorted({r, -r})
    return [r]


def _quadratic_roots(a: int, b: int, c: int, dom: str) -> list[int]:
    """Integer y in the domain with a y^2 + b y + c = 0, a != 0 (direct, for ground truth)."""
    disc = b * b - 4 * a * c
    if disc < 0 or not is_square(disc):
        return []
    s = isqrt(disc)
    out = set()
    for m in {s, -s}:
        if (m - b) % (2 * a) == 0:
            y = (m - b) // (2 * a)
            if DOMAINS[dom](y):
                out.add(y)
    return sorted(out)


# ---------------------------------------------------------------------------
# reduction steps
# ---------------------------------------------------------------------------

@dataclass
class Step:
    name: str
    forward: str
    backward: str
    admissibility: str
    lean: list[str]
    back: Callable[[int, list[int]], list[int]]   # (n, reduced witnesses) -> original witnesses
    filter_trivial: bool                           # the way back never rejects a reduced solution

    def explain(self) -> dict:
        return {'step': self.name, 'forward': self.forward, 'backward': self.backward,
                'admissibility': self.admissibility, 'lean': self.lean,
                'filter_trivial': self.filter_trivial}


def quadratic_step(a: int, b: int, c: int, F, dom: str) -> tuple[Step, PowerConstraint]:
    """a y^2 + b y + c = F(n)  ->  m^2 = 4a F(n) + b^2 - 4ac, m = 2ay + b (both signs of m)."""
    if a == 0:
        raise ValueError('a != 0 required')
    G = padd(pscale(F, 4 * a), (b * b - 4 * a * c,))

    def back(n: int, ms: list[int]) -> list[int]:
        out = set()
        for m in set(ms) | {-m for m in ms}:
            if (m - b) % (2 * a) == 0:
                y = (m - b) // (2 * a)
                if DOMAINS[dom](y):
                    out.add(y)
        return sorted(out)
    # a = +-1 and y in Z: m^2 = b^2 (mod 4) forces m = b (mod 2), so 2a | m - b always
    trivial = abs(a) == 1 and dom == 'int'
    step = Step('quadratic discriminant', f'm = 2*{a}*y + {b}',
                f'y = (m - {b}) / {2 * a}',
                f'{2 * a} | m - {b} for m or -m, and y in {_domain_text(dom)}',
                ['PerfectPower.Reduction.quadratic'], back, trivial)
    return step, PowerConstraint(G, 2)


def triangular_step(F, dom: str) -> tuple[Step, PowerConstraint]:
    """y (y + 1) / 2 = F(n)  ->  m^2 = 8 F(n) + 1, m = 2y + 1."""
    G = padd(pscale(F, 8), (1,))

    def back(n: int, ms: list[int]) -> list[int]:
        out = set()
        for m in set(ms) | {-m for m in ms}:
            y = (m - 1) // 2                      # m is odd since m^2 = 8F + 1
            if DOMAINS[dom](y):
                out.add(y)
        return sorted(out)
    # an odd m gives y = (m-1)/2 and -1-y = (-m-1)/2, one of which is >= 0; 'pos' can fail (y = 0)
    trivial = dom in ('int', 'nonneg')
    step = Step('triangular', 'm = 2*y + 1', 'y = (m - 1) / 2',
                'none: m^2 = 8F+1 forces m odd' + ('' if trivial else '; y >= 1 still checked'),
                ['PerfectPower.Reduction.triangular', 'PerfectPower.Reduction.triangular_count_int',
                 'PerfectPower.Reduction.triangular_count_nonneg'], back, trivial)
    return step, PowerConstraint(G, 2)


# ---------------------------------------------------------------------------
# complete argument sets proved in Lean:  t^3 + k = m^2  <=>  t in T
# ---------------------------------------------------------------------------

_MORDELL = {
    -2: ({3: [5]}, ['PerfectPower.MordellMinus2.points', 'PerfectPower.Transport.complete_cube_sub_two']),
    -4: ({2: [2], 5: [11]}, ['PerfectPower.MordellMinus4.points']),
    -5: ({}, ['PerfectPower.MordellMinus5.no_points']),
    -6: ({}, ['PerfectPower.MordellMinus6.no_points']),
    -13: ({17: [70]}, ['PerfectPower.MordellMinus13.points',
                       'PerfectPower.Transport.complete_cube_sub_thirteen']),
}


def _generated_no_points() -> dict[int, str]:
    path = ROOT / 'PerfectPower' / 'Generated' / 'MordellDescent.lean'
    out = {}
    if path.exists():
        for sign, digits in re.findall(r'theorem no_points_([mp])(\d+)', path.read_text()):
            k = int(digits) * (-1 if sign == 'm' else 1)
            out[k] = f'PerfectPower.Generated.no_points_{sign}{digits}'
    return out


_NO_POINTS = None


def mordell_complete(k: int):
    """({t: [m >= 0]}, lean names) when y^2 = t^3 + k is solved completely in Lean, else None."""
    global _NO_POINTS
    if k in _MORDELL:
        return _MORDELL[k]
    if k < 0 and (-k) % 432 == 0:
        u6 = (-k) // 432
        u = integer_power_root(u6, 6)
        if u is not None and u > 0:
            return ({12 * u * u: [36 * u ** 3]}, ['PerfectPower.MordellFLT3.points',
                                                  'PerfectPower.Transport.complete_fermat'])
    if _NO_POINTS is None:
        _NO_POINTS = _generated_no_points()
    if k in _NO_POINTS:
        return ({}, [_NO_POINTS[k], 'PerfectPower.Transport.complete_of_no_points'])
    return None


def match_affine_cube(F) -> tuple[int, int, int] | None:
    """(r, s, k) with F(n) = (r n + s)^3 + k exactly, r != 0, or None."""
    F = _trim(F)
    if len(F) != 4:
        return None
    a0, a1, a2, a3 = F
    r = integer_power_root(a3, 3)
    if r is None or r == 0:
        return None
    if a2 % (3 * r * r):
        return None
    s = a2 // (3 * r * r)
    if a1 != 3 * r * s * s:
        return None
    return r, s, a0 - s ** 3


# ---------------------------------------------------------------------------
# certificates
# ---------------------------------------------------------------------------

def find_certificate(F, d: int):
    """(path, Lean theorem) of a committed pp-cert/1 certificate for (F, d), or None."""
    F = list(_trim(F))
    for path in sorted((ROOT / 'certs').glob('*/*.json')):
        try:
            obj = json.loads(path.read_text())
        except (OSError, ValueError):
            continue
        st = obj.get('statement', {})
        if list(st.get('F', [])) == F and st.get('d') == d:
            return (str(path.relative_to(ROOT)), f"PerfectPower.Generated.{obj['name']}",
                    list(st.get('hits', [])))
    return None


# ---------------------------------------------------------------------------
# Pell orbit generation
# ---------------------------------------------------------------------------

@dataclass
class PellBranch:
    """A n^2 + B n + C = m^2 via X = 2An + B, X^2 - D m^2 = Delta, D = 4A."""
    A: int
    B: int
    C: int
    D: int
    Delta: int
    unit: tuple[int, int]
    seeds: list[tuple[int, int]]

    def explain(self) -> dict:
        x1, y1 = self.unit
        return {'quadratic': [self.A, self.B, self.C], 'D': self.D, 'Delta': self.Delta,
                'unit': list(self.unit), 'seeds': [list(s) for s in self.seeds],
                'transition': f'(X, Y) -> ({x1}*X + {self.D * y1}*Y, {y1}*X + {x1}*Y)',
                'admissible': f'X = {self.B} (mod {2 * self.A}), n = (X - {self.B}) / {2 * self.A} >= 1',
                'step_in_n_m': (f"n' = {x1}*n + {2 * y1}*m + {self.B * (x1 - 1)}/{2 * self.A},  "
                                f"m' = {2 * self.A * y1}*n + {x1}*m + {self.B * y1}"),
                'small_n_checked_directly': self.small_n()}

    def good_fraction(self) -> Fraction:
        """Sum over seeds of (admissible residues X = B mod 2A in one period) / period.  Positive
        iff the branch has infinitely many hits (`branch_infinite_iff`)."""
        M = 2 * self.A
        x1, y1 = self.unit
        total = Fraction(0)
        for X, Y in self.seeds:
            s0 = (X % M, Y % M)
            st, period, good = s0, 0, 0
            while True:
                if st[0] == self.B % M:
                    good += 1
                period += 1
                st = ((st[0] * x1 + self.D * st[1] * y1) % M, (st[0] * y1 + st[1] * x1) % M)
                if st == s0:
                    break
            total += Fraction(good, period)
        return total

    def small_n(self) -> int:
        """n <= this bound may have X = 2An + B <= 0; they are tested directly."""
        return max(0, -self.B // (2 * self.A) + 1) if self.B < 0 else 0

    def hits(self, N: int) -> dict[int, list[int]]:
        """{n: [m >= 0]} for 1 <= n <= N, from the orbits (no scan beyond small_n)."""
        A, B, C, D = self.A, self.B, self.C, self.D
        x1, y1 = self.unit
        out: dict[int, set[int]] = {}
        for n in range(1, min(N, self.small_n()) + 1):
            v = A * n * n + B * n + C
            if v >= 0 and is_square(v):
                out.setdefault(n, set()).add(isqrt(v))
        Xmax = 2 * A * N + B
        for X0, Y0 in self.seeds:
            # walk down while X > 0 and Y >= 0, then up until X exceeds the bound
            X, Y = X0, Y0
            while True:
                pX, pY = X * x1 - D * Y * y1, -X * y1 + Y * x1
                if pX > 0 and pY >= 0:
                    X, Y = pX, pY
                else:
                    break
            while X <= Xmax:
                if X > 0 and Y >= 0 and (X - B) % (2 * A) == 0:
                    n = (X - B) // (2 * A)
                    if 1 <= n <= N:
                        out.setdefault(n, set()).add(Y)
                X, Y = X * x1 + D * Y * y1, X * y1 + Y * x1
        return {n: sorted(ms) for n, ms in out.items()}


def pell_branch(A: int, B: int, C: int) -> PellBranch:
    D = 4 * A
    Delta = B * B - 4 * A * C
    x1, y1 = pell_fundamental(D)
    seeds = []
    for X, Y in _positive_orbits(D, Delta):
        # orbit representatives with eta > 0; move each to Y >= 0
        while Y < 0:
            X, Y = X * x1 + D * Y * y1, X * y1 + Y * x1
        seeds.append((X, Y))
    return PellBranch(A, B, C, D, Delta, (x1, y1), sorted(set(seeds)))


# ---------------------------------------------------------------------------
# plans
# ---------------------------------------------------------------------------

@dataclass
class Plan:
    original: object
    chain: list[Step]
    reduced: PowerConstraint
    method: str
    status: str
    justification: list[str]
    data: dict = field(default_factory=dict)
    exact_to_any_N: bool = True
    execution_verified: bool = False
    _reduced_hits: Callable[[int], dict[int, list[int]]] | None = None
    _reduced_contains: Callable[[int], bool] | None = None
    _finite_list: dict[int, list[int]] | None = None

    # ---- operations ----------------------------------------------------------------------
    @property
    def supports(self) -> list[str]:
        ops = ['contains', 'explain', 'bounded_evidence']
        if self.exact_to_any_N and self._reduced_hits is not None:
            ops += ['iter_hits', 'count']
        if self._finite_list is not None:
            ops.append('all_hits')
        return ops

    def _pull(self, n: int, ms: list[int]) -> list[int]:
        for step in reversed(self.chain):
            ms = step.back(n, ms)
            if not ms:
                return []
        return ms

    def contains(self, n: int) -> list[int]:
        """Original witnesses at n ([] if n is not a solution)."""
        if n < 1:
            return []
        if self._reduced_contains is not None and not self._reduced_contains(n):
            return []
        return self._pull(n, self.reduced.witnesses(n))

    def iter_hits(self, N: int) -> Iterator[tuple[int, list[int]]]:
        if 'iter_hits' not in self.supports:
            raise NotEnumerable(f'{self.status}: no enumeration ({self.method})')
        red = self._reduced_hits(N)
        for n in sorted(red):
            ws = self._pull(n, red[n])
            if ws:
                yield n, ws

    def count(self, N: int) -> int:
        if 'count' not in self.supports:
            raise NotEnumerable(f'{self.status}: no count ({self.method})')
        if not self.chain and self.data.get('fast_count'):
            return structural_count(self.reduced.F, self.reduced.d, N)
        return sum(1 for _ in self.iter_hits(N))

    def all_hits(self) -> list[tuple[int, list[int]]]:
        if self._finite_list is None:
            raise NotEnumerable(f'{self.status}: no complete finite list')
        out = []
        for n in sorted(self._finite_list):
            ws = self._pull(n, self._finite_list[n])
            if ws:
                out.append((n, ws))
        return out

    def bounded_evidence(self, N: int) -> dict:
        """A labelled direct scan of 1 <= n <= N.  Never a completeness claim."""
        hits = [(n, w) for n in range(1, N + 1) if (w := self.original.witnesses(n))]
        return {'label': BOUNDED_EVIDENCE, 'N': N, 'hits': hits,
                'claim': f'these are the solutions with n <= {N}; nothing is claimed beyond'}

    def explain(self) -> dict:
        return {'constraint': self.original.describe(),
                'reductions': [s.explain() for s in self.chain],
                'reduced': self.reduced.describe(), 'method': self.method,
                'status': self.status, 'justification': self.justification,
                'supports': self.supports, 'execution_verified': self.execution_verified,
                'data': self.data}


def _lift_status(status: str, chain: list[Step]) -> str:
    """A nontrivial admissibility filter keeps finite answers complete but can empty an infinite
    family, so infinitude is no longer asserted."""
    if status == STRUCTURED_INFINITE and not all(s.filter_trivial for s in chain):
        return STRUCTURED_FILTERED
    return status


def _power_plan(pc: PowerConstraint) -> dict:
    """Solver for F(n) = m^d: method, status, justification, data and the operations."""
    F, d = pc.F, pc.d
    # 1. affine transport to a Mordell curve solved in Lean
    if d == 2:
        m = match_affine_cube(F)
        if m is not None:
            r, s, k = m
            solved = mordell_complete(k)
            if solved is not None:
                T, lean = solved
                hits = {}
                for t, ms in T.items():
                    if (t - s) % r == 0 and (t - s) // r >= 1:
                        hits[(t - s) // r] = sorted({x for mm in ms for x in (mm, -mm)})
                return dict(method='affine transport to a solved Mordell curve',
                            status=COMPLETE_FINITE,
                            justification=lean + ['PerfectPower.Transport.affine_count',
                                                  'PerfectPower.Reduction.affine'],
                            data={'substitution': f't = {r}*n + ({s})', 'curve': f'm^2 = t^3 + ({k})',
                                  'complete_arguments': sorted(T),
                                  'specialized_test': ' or '.join(f'{r}*n + ({s}) == {t}' for t in sorted(T))
                                  or 'False'},
                            finite=hits, contains=lambda n: (r * n + s) in T,
                            hits=lambda N: {n: w for n, w in hits.items() if n <= N})
    if d == 2 and len(F) == 3 and F[2] > 0 and not is_square(F[2]) and F[1] ** 2 - 4 * F[2] * F[0]:
        return _quadratic_pell_plan(pc)
    cl = classify(F, d)
    kind = cl.kind
    base = {'atlas_kind': kind, 'growth': cl.growth}
    if kind in ('constant', 'power') and cl.infinite:
        return dict(method='identity: F = c G^d with c a d-th power, every n is a hit',
                    status=STRUCTURED_INFINITE, justification=['atlas classification (Python)'],
                    data={**base, 'fast_count': True},
                    hits=lambda N: {n: pc.witnesses(n) for n in range(1, N + 1)})
    if kind in ('constant', 'power'):
        zeros = {n: [0] for n in _positive_zeros(F)} if kind == 'power' else {}
        return dict(method='twisted power: only the zeros of F', status=COMPLETE_FINITE,
                    justification=['atlas classification (Python)'], data=base, finite=zeros,
                    hits=lambda N: {n: w for n, w in zeros.items() if n <= N})
    if kind == 'radical':
        info = cl.details

        def hits(N):
            ns = set(_positive_zeros(F, N)) | _radical_param_hits(info, N)
            return {n: pc.witnesses(n) for n in sorted(ns)}
        just = ['PerfectPower.RationalYun.Decomposition.radical_count',
                'PerfectPower.RationalYun.Decomposition.radical_count_explicit',
                'PerfectPower.RationalYun.Decomposition.radical_kappa_decide']
        data = {**base, 'fast_count': True,
                'parametrization': f"n = (s*{info['z0']}*w^{info['t']} + ({info['u']})) / {info['v']}, "
                                   "s in signs, w in good_residues_mod_v (mod v)",
                'signs': info['signs'], 'good_residues_mod_v': info['good_residues_mod_v'],
                'kappa': info['kappa']}
        if cl.infinite:
            return dict(method='radical parametrization', status=STRUCTURED_INFINITE,
                        justification=just, data=data, hits=hits)
        # finitely many: the zeros and the negative-sign branch, both bounded
        bound = max([abs(info['u'])] + _positive_zeros(F)) + 1
        fin = hits(bound)
        return dict(method='radical type, no admissible class', status=COMPLETE_FINITE,
                    justification=just, data=data, finite=fin,
                    hits=lambda N: {n: w for n, w in fin.items() if n <= N})
    if kind == 'pell':
        branches, bounded = [], []
        quads = [(q['A'], q['B'], q['C'], q['case']) for q in cl.details['quadratics']]
        for A, B, C, case in quads:
            if case == 'pell':
                branches.append(pell_branch(A, B, C))
            else:
                bounded.append((A, B, C))

        def hits(N):
            ns: set[int] = set(_positive_zeros(F, N))
            for br in branches:
                ns |= set(br.hits(N))
            for (A, B, C) in bounded:
                ns |= quadratic_square_hits(A, B, C, N)
            return {n: pc.witnesses(n) for n in sorted(ns)}
        just = ['PerfectPower.RationalYun.Decomposition.pell_count',
                'PerfectPower.RationalYun.Decomposition.pell_count_explicit',
                'PerfectPower.RationalYun.Decomposition.pell_kappa_decide']
        data = {**base, 'branches': [b.explain() for b in branches],
                'bounded_branches': [list(t) for t in bounded], 'kappa': cl.details['kappa']}
        if cl.infinite:
            return dict(method='Pell orbits', status=STRUCTURED_INFINITE, justification=just,
                        data=data, hits=hits)
        # every Pell branch is unpopulated: hits come from bounded branches, zeros and the
        # finitely many small n of the Pell branches
        bound = max([1] + _positive_zeros(F) + [br.small_n() for br in branches]
                    + [max(quadratic_square_hits(A, B, C, 10 ** 6) | {0}) for A, B, C in bounded])
        fin = hits(bound)
        return dict(method='Pell type with no populated branch', status=COMPLETE_FINITE,
                    justification=just, data=data, finite=fin,
                    hits=lambda N: {n: w for n, w in fin.items() if n <= N})
    # finite type
    cert = find_certificate(F, d)
    strategy = cl.details.get('strategy')
    if cl.effective and strategy[0] == 'runge':
        from .runge import runge_enumerate
        e = strategy[1]
        fin = {n: pc.witnesses(n) for n, _ in runge_enumerate(F, e).hits
               if pc.witnesses(n)}
        just = ([cert[1], f'certificate {cert[0]} (pp-cert/1)'] if cert else []) + \
            ['Runge enumeration (Python, runge.runge_enumerate)']
        return dict(method=f'Runge enumeration (divisor {e})', status=COMPLETE_FINITE,
                    justification=just, data={**base, 'certificate': cert and cert[0]},
                    finite=fin, hits=lambda N: {n: w for n, w in fin.items() if n <= N})
    if cl.effective:
        return dict(method=f'exact root reduction {strategy[:2]}', status=CLASSIFIED_FINITE,
                    justification=['Siegel via Theorem G (finite)', 'atlas structural_hits (Python)'],
                    data=base, hits=lambda N: {n: pc.witnesses(n)
                                               for n in structural_hits(F, d, N)})
    return dict(method='finite by Siegel (Theorem G); no effective enumeration here',
                status=NOT_ENUMERATED, justification=['Siegel via Theorem G (paper; not in Lean)'],
                data={**base, 'curve': cl.curve}, hits=None)


def _quadratic_pell_plan(pc: PowerConstraint) -> dict:
    """A n^2 + B n + C = m^2 with A > 0 not a square and nonzero discriminant, in its own
    coordinates (no rescaling)."""
    C, B, A = pc.F
    br = pell_branch(A, B, C)
    g = br.good_fraction()
    x1, y1 = br.unit
    # eps = x1 + y1 sqrt(D) = 2 x1 - 1/eps, so log(2 x1) is exact to float precision for large x1
    log_eps = log(x1 + y1 * sqrt(br.D)) if x1 < 10 ** 15 else log(2 * x1)
    data = {'atlas_kind': 'pell', 'growth': 'log N' if g else 'bounded',
            'branches': [br.explain()], 'bounded_branches': [],
            'good_fraction': str(g), 'kappa': float(g) / log_eps if g else 0.0}
    just = ['PerfectPower.PellExact.pell_branch_explicit',
            'PerfectPower.RationalYun.branch_infinite_iff',
            'PerfectPower.RationalYun.branch_infinite_iff_bounded']

    def hits(N):
        return {n: pc.witnesses(n) for n in sorted(br.hits(N))}
    if g:
        return dict(method='Pell orbits', status=STRUCTURED_INFINITE, justification=just,
                    data=data, hits=hits)
    # no orbit element is admissible: only the small n with 2An + B <= 0 can hit
    fin = hits(max(1, br.small_n()))
    return dict(method='Pell type with no populated branch', status=COMPLETE_FINITE,
                justification=just, data=data, finite=fin,
                hits=lambda N: {n: w for n, w in fin.items() if n <= N})


def compile_constraint(con) -> Plan:
    if isinstance(con, PowerConstraint):
        chain, reduced = [], con
    elif isinstance(con, TriangularConstraint):
        step, reduced = triangular_step(con.F, con.y_domain)
        chain = [step]
    elif isinstance(con, QuadraticRootConstraint):
        step, reduced = quadratic_step(con.a, con.b, con.c, con.F, con.y_domain)
        chain = [step]
    else:
        raise TypeError(f'unsupported constraint {con!r}')
    if reduced.d < 2:
        raise ValueError('d >= 2 required')
    if len(_trim(reduced.F)) == 1:
        v = _trim(reduced.F)[0]
        ok = bool(_power_witnesses(v, reduced.d))
        solver = dict(method='constant', status=STRUCTURED_INFINITE if ok else COMPLETE_FINITE,
                      justification=['direct evaluation'], data={},
                      finite=None if ok else {},
                      hits=lambda N: {n: reduced.witnesses(n) for n in range(1, N + 1)} if ok else {})
    else:
        solver = _power_plan(reduced)
    status = _lift_status(solver['status'], chain)
    return Plan(original=con, chain=chain, reduced=reduced, method=solver['method'],
                status=status, justification=[j for s in chain for j in s.lean] + solver['justification'],
                data=solver['data'], exact_to_any_N=solver['hits'] is not None,
                _reduced_hits=solver['hits'], _reduced_contains=solver.get('contains'),
                _finite_list=solver.get('finite'))
