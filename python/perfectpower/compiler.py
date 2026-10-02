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
  CONDITIONAL_COMPLETE      a complete finite list from a Lean theorem that assumes named
                            premises (Matveev's lower bound); the premises are listed in the plan
  NOT_ENUMERATED            finitely many solutions (Siegel via Theorem G) and no effective
                            enumeration here; only bounded_evidence(N), labelled as such

Plan.answer folds these into the four answers a consumer acts on: `complete_list`, `generator`,
`conditional` (with its premises) and `unresolved`.  Plan.certificate states the boundary: the Lean
theorems, the named premises, the Python reduction steps, and that execution is not verified.

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
CONDITIONAL_COMPLETE = 'CONDITIONAL_COMPLETE'
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


def _generated_complete() -> dict[int, tuple]:
    """k -> ({t: [m >= 0]}, lean names) for every complete list `y^2 = x^3 - D` in the solved-family
    registry `receipts/mordell_registry.json`.  The registry is structured data from the generators'
    receipts, and `python/make_mordell_registry.py` checks every entry against its Lean theorem
    statement (full parse, both directions) and fails on any gap, so a missing or stale registry
    can only make the compiler more conservative, never wrong."""
    path = ROOT / 'receipts' / 'mordell_registry.json'
    out = {}
    if not path.exists():
        return out
    reg = json.loads(path.read_text())
    for c in reg['curves']:
        out[-c['D']] = (_table(c['points']), [c['lean'], c['via']])
    for c in reg.get('positive_curves', []):
        out[c['k']] = (_table(c['points']), [c['lean'], 'PerfectPower.PositiveKCurve.complete_of_sols'])
    return out


def _table(points) -> dict[int, list[int]]:
    T: dict[int, list[int]] = {}
    for x, y in points:
        T.setdefault(x, [])
        if y >= 0:
            T[x].append(y)
    return {t: sorted(ms) for t, ms in T.items()}


def mordell_conditional(k: int):
    """({t: [m >= 0]}, lean names, premises) when y^2 = t^3 + k has a complete list in Lean
    conditional on named Matveev hypotheses (`receipts/mordell_registry.json`, conditional_curves)."""
    path = ROOT / 'receipts' / 'mordell_registry.json'
    if not path.exists():
        return None
    for c in json.loads(path.read_text()).get('conditional_curves', []):
        if -c['D'] == k:
            return (_table(c['points']), [c['lean'], 'PerfectPower.DescentThueList.complete_of_lists'],
                    c['premises'])
    return None


_NO_POINTS = None
_COMPLETE = None


def mordell_complete(k: int):
    """({t: [m >= 0]}, lean names) when y^2 = t^3 + k is solved completely in Lean, else None."""
    global _NO_POINTS, _COMPLETE
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
    if _COMPLETE is None:
        _COMPLETE = _generated_complete()
    if k in _COMPLETE:
        return _COMPLETE[k]
    return None


def mordell_family_match(k: int, window: int = 4000):
    """(t, m, certificate) with k = (4t - 1)^3 - 4m^2 and m free of primes = 3 (mod 4), found by
    searching c = 4t - 1 above the cube root of k (a bounded search: membership is certified by
    the returned data, non-membership is not claimed).  Certificate: m = 2^j m1, m1 | u^2 + 1."""
    from .arith import sqrt_mod
    lo = _icbrt(k) + 1
    lo += (3 - lo) % 4
    for c in range(lo, lo + 4 * window, 4):
        v = c ** 3 - k
        if v <= 0 or v % 4:
            continue
        m2 = v // 4
        m = isqrt(m2)
        if m * m != m2 or m == 0:
            continue
        j, m1 = 0, m
        while m1 % 2 == 0:
            j, m1 = j + 1, m1 // 2
        roots = sqrt_mod((-1) % m1, m1) if m1 > 1 else [0]
        if not roots:
            continue
        return {'t': (c + 1) // 4, 'c': c, 'm': m, 'j': j, 'm1': m1, 'u': roots[0]}
    return None


def _icbrt(k: int) -> int:
    """floor of the real cube root of k."""
    if k < 0:
        r = -_icbrt(-k)
        return r if r ** 3 == k else r - 1
    if k < 2:
        return k
    r = 1 << -(-k.bit_length() // 3)   # 2^ceil(bits/3) >= cube root: Newton descends from above
    while True:
        s = (2 * r + k // (r * r)) // 3
        if s >= r:
            break
        r = s
    while r ** 3 > k:
        r -= 1
    while (r + 1) ** 3 <= k:
        r += 1
    return r


def missing_premise(F, d: int) -> dict | None:
    """For a genus-one plan that cannot be enumerated: the exact statement that would finish it."""
    F = _trim(F)
    if d == 2 and len(F) == 4:
        e, c, b, a = F
        A, B = 81 * a * c - 27 * b * b, 54 * b ** 3 - 243 * a * b * c + 729 * a * a * e
        return {'kind': 'genus one, cubic',
                'model': f'V^2 = U^3 + ({A}) U + ({B})',
                'substitution': f'U = {9 * a}*n + ({3 * b}), V = {27 * a}*m',
                'premise': f'Transport.IntegralPointsOnImage {a} {b} {A} {B} L: every integral point '
                           f'of the model with {9 * a} | U - ({3 * b}) and {27 * a} | V is in the list L',
                'consumer': 'PerfectPower.Transport.cubic_sound_image (with Genus1.cubicOK checking L)',
                'routes': ['a Mordell-Weil basis proved complete, an elliptic-logarithm bound on '
                           'integral points, and a sieve down to a finite search',
                           'a descent in a quadratic ring or a class-group argument, when the model is '
                           'a Mordell curve (as in MordellMinus2, ClassTwo)',
                           'Runge, when the curve is Runge-rigid']}
    if d == 2 and len(F) == 5:
        return {'kind': 'genus one, quartic',
                'premise': 'a complete list of integral points on the quartic model; no Lean interface '
                           'for quartic models yet (OPEN_PROBLEMS item 10)',
                'routes': ['Runge, when the leading coefficient is a square',
                           'reduction to a cubic model with the images of the integral points tracked']}
    return {'kind': 'higher genus or superelliptic',
            'premise': 'an effective bound on integral points (Baker-type) or a Runge condition; '
                       'Siegel gives finiteness only'}


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

    def unit_power(self, j: int) -> tuple[int, int]:
        """(x, y) with x + y sqrt(D) = eps^j, by fast exponentiation (O(log j) products)."""
        x1, y1 = self.unit
        rx, ry, bx, by = 1, 0, x1, y1
        while j:
            if j & 1:
                rx, ry = rx * bx + self.D * ry * by, rx * by + ry * bx
            bx, by = bx * bx + self.D * by * by, 2 * bx * by
            j >>= 1
        return rx, ry

    def point(self, k: int, j: int) -> dict:
        """The j-th point of the orbit of seed k: (X, Y) = seed * eps^j, and its index n when
        X = 2An + B with n >= 1 (else None)."""
        X0, Y0 = self.seeds[k]
        ex, ey = self.unit_power(j)
        X, Y = X0 * ex + self.D * Y0 * ey, X0 * ey + Y0 * ex
        n = None
        if X > 0 and (X - self.B) % (2 * self.A) == 0 and (X - self.B) // (2 * self.A) >= 1:
            n = (X - self.B) // (2 * self.A)
        return {'seed': k, 'j': j, 'X': X, 'Y': abs(Y), 'n': n}

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


def bounded_branch_hits(A: int, B: int, C: int) -> list[int]:
    """All n >= 1 with A n^2 + B n + C a square, for a bounded branch (A < 0, or A a positive
    square, nonzero discriminant).  The search limit is the proved bound, never a fixed cutoff:
    n <= |B| + |C| for A < 0 (`hit_le_of_neg`) and n <= |Delta| + |B| for A a square
    (`hit_le_of_square`).  quadratic_square_hits only enumerates divisors or the ellipse, so the
    size of the limit costs nothing."""
    Delta = B * B - 4 * A * C
    if A < 0:
        # A n^2 + B n + C >= 0 forces |2An + B| <= sqrt(Delta): scan only that interval
        # (inside the proved bound n <= |B| + |C|, `hit_le_of_neg`)
        if Delta < 0:
            return []
        r = isqrt(Delta)
        ends = [Fraction(-r - B, 2 * A), Fraction(r - B, 2 * A)]
        lo = max(1, -((-min(ends).numerator) // min(ends).denominator))
        hi = min(abs(B) + abs(C), max(ends).numerator // max(ends).denominator)
        return [n for n in range(lo, hi + 1)
                if (v := A * n * n + B * n + C) >= 0 and is_square(v)]
    if A > 0 and is_square(A):
        limit = abs(Delta) + abs(B)
    else:
        raise ValueError('not a bounded branch')
    return sorted(quadratic_square_hits(A, B, C, limit))


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

    def orbit_point(self, k: int, j: int) -> dict:
        """Direct access to the j-th point of the k-th Pell orbit (Pell plans only), with the
        original witnesses it yields after the backward maps (empty if it is inadmissible)."""
        brs = self.data.get('branches') or []
        if not brs:
            raise NotEnumerable('orbit_point needs a Pell plan')
        b = brs[0]
        br = PellBranch(b['quadratic'][0], b['quadratic'][1], b['quadratic'][2], b['D'],
                        b['Delta'], tuple(b['unit']), [tuple(x) for x in b['seeds']])
        pt = br.point(k, j)
        pt['witnesses'] = self._pull(pt['n'], [pt['Y']]) if pt['n'] is not None else []
        return pt

    def bounded_evidence(self, N: int) -> dict:
        """A labelled direct scan of 1 <= n <= N.  Never a completeness claim."""
        hits = [(n, w) for n in range(1, N + 1) if (w := self.original.witnesses(n))]
        return {'label': BOUNDED_EVIDENCE, 'N': N, 'hits': hits,
                'claim': f'these are the solutions with n <= {N}; nothing is claimed beyond'}

    def galois(self) -> dict:
        """The Galois orbits of the roots of the reduced polynomial and why they give this type
        (galois.galois_profile)."""
        from .galois import galois_profile
        prof = galois_profile(self.reduced.F, self.reduced.d)
        cert = self.data.get('descent')
        if cert:
            # the symmetry that drives the proof: the conjugate factors of x^3 in the ring
            prof['descent'] = {k: cert[k] for k in ('field', 'ring', 'factorization', 'units',
                                                     'class_number', 'j', 'points', 'why')}
            prof['explanation'] = prof['explanation'] + ' ' + cert['why']
        return prof

    @property
    def mechanism(self) -> str:
        """The solution mechanism, in one of three kinds."""
        if self.status == COMPLETE_FINITE:
            return 'complete finite list, with a proof that no solution is missed'
        if self.status in (STRUCTURED_INFINITE, STRUCTURED_FILTERED):
            return 'infinite family: ' + ('a counting law (Pell orbits)' if 'Pell' in self.method
                                          else 'an exact generator')
        if self.status == CONDITIONAL_COMPLETE:
            return 'complete finite list conditional on named premises: ' + ', '.join(self.data.get('premises', []))
        if self.status == NOT_ENUMERATED:
            return 'missing premise: ' + (self.data.get('missing_premise') or {}).get('premise', '?')
        return 'finite, exact to any N, no complete list'

    @property
    def answer(self) -> str:
        """One of the four answers a consumer acts on."""
        if self.status == COMPLETE_FINITE:
            return 'complete_list'
        if self.status in (STRUCTURED_INFINITE, STRUCTURED_FILTERED):
            return 'generator'
        if self.status == CONDITIONAL_COMPLETE:
            return 'conditional'
        return 'unresolved'

    @property
    def certificate(self) -> dict:
        """The certificate boundary: what is proved where, and what is assumed."""
        lean = [j for j in self.justification if j.startswith('PerfectPower.')]
        return {'answer': self.answer,
                'lean_theorems': lean,
                'premises': list(self.data.get('premises', [])),
                'missing_premise': (self.data.get('missing_premise') or {}).get('premise'),
                'python_steps': [s.explain() for s in self.chain] + [self.method],
                'python_only': [j for j in self.justification if not j.startswith('PerfectPower.')],
                'execution_verified': self.execution_verified}

    def explain(self, galois: bool = False) -> dict:
        extra = {'galois': self.galois()} if galois else {}
        return {**extra, 'answer': self.answer, 'certificate': self.certificate,
                'mechanism': self.mechanism, 'constraint': self.original.describe(),
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
            cond = mordell_conditional(k)
            if cond is not None:
                T, lean, prem = cond
                hits = {}
                for t, ms in T.items():
                    if (t - s) % r == 0 and (t - s) // r >= 1:
                        hits[(t - s) // r] = sorted({x for mm in ms for x in (mm, -mm)})
                return dict(method='affine transport to a Mordell curve complete under named premises',
                            status=CONDITIONAL_COMPLETE,
                            justification=lean + ['PerfectPower.Transport.affine_count',
                                                  'PerfectPower.Reduction.affine'],
                            data={'substitution': f't = {r}*n + ({s})', 'curve': f'm^2 = t^3 + ({k})',
                                  'premises': prem,
                                  'premise_meaning': "instances of Matveev's lower bound for linear forms "
                                                     'in logarithms, stated in Lean and not proved there',
                                  'complete_arguments': sorted(T),
                                  'specialized_test': ' or '.join(f'{r}*n + ({s}) == {t}' for t in sorted(T))
                                  or 'False'},
                            finite=hits, contains=lambda n: (r * n + s) in T,
                            hits=lambda N: {n: w for n, w in hits.items() if n <= N})
            fam = mordell_family_match(k)
            if fam is not None:
                return dict(method="Mordell's family k = (4t - 1)^3 - 4m^2 (no integral points)",
                            status=COMPLETE_FINITE,
                            justification=['PerfectPower.MordellFamily.family_not_isHit',
                                           'PerfectPower.MordellFamily.no_points_cert'],
                            data={'substitution': f't = {r}*n + ({s})', 'curve': f'm^2 = t^3 + ({k})',
                                  'family': fam, 'specialized_test': 'False'},
                            finite={}, contains=lambda n: False, hits=lambda N: {})
            if k < 0:
                from .descent import certificate as descent_certificate, affine_hits
                cert = descent_certificate(-k)
                if cert is not None:
                    fin: dict[int, list[int]] = {}
                    for n, mm in affine_hits(cert, r, s):
                        fin.setdefault(n, []).append(mm)
                    fin = {n: sorted(ms) for n, ms in fin.items()}
                    T = sorted({x for x, _ in cert['points']})
                    return dict(method=f'descent in Z[sqrt(-{-k})] (certificate discovered here, checked in Lean)',
                                status=COMPLETE_FINITE,
                                justification=['PerfectPower.Descent.hits_of_cert',
                                               'PerfectPower.Descent.complete_of_cert',
                                               'PerfectPower.Descent.image_of_complete',
                                               'PerfectPower.Transport.cubic_sound_image'],
                                data={'substitution': f't = {r}*n + ({s})', 'curve': f'm^2 = t^3 + ({k})',
                                      'descent': cert, 'complete_arguments': T,
                                      'specialized_test': ' or '.join(f'{r}*n + ({s}) == {t}' for t in T)
                                      or 'False'},
                                finite=fin, contains=lambda n, T=T: (r * n + s) in T,
                                hits=lambda N, fin=fin: {n: w for n, w in fin.items() if n <= N})
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
                ns |= {n for n in bounded_branch_hits(A, B, C) if n <= N}
            return {n: pc.witnesses(n) for n in sorted(ns)}
        just = ['PerfectPower.RationalYun.hit_le_of_neg', 'PerfectPower.RationalYun.hit_le_of_square'] * bool(bounded) + [
                'PerfectPower.RationalYun.Decomposition.pell_count',
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
                    + [max(bounded_branch_hits(A, B, C) + [0]) for A, B, C in bounded])
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
        try:
            enum = runge_enumerate(F, e)
        except ValueError as exc:
            # the Runge threshold is effective but its direct-scan prefix is too long here
            return dict(method=f'Runge-rigid (divisor {e}), prefix too long to enumerate',
                        status=NOT_ENUMERATED,
                        justification=['Runge (Theorem R): finite and effective in principle'],
                        data={**base, 'reason': str(exc)}, hits=None)
        fin = {n: pc.witnesses(n) for n, _ in enum.hits if pc.witnesses(n)}
        just = ([cert[1], f'certificate {cert[0]} (pp-cert/1)'] if cert else []) + \
            ['Runge enumeration (Python, runge.runge_enumerate)']
        return dict(method=f'Runge enumeration (divisor {e})', status=COMPLETE_FINITE,
                    justification=just, data={**base, 'certificate': cert and cert[0]},
                    finite=fin, hits=lambda N: {n: w for n, w in fin.items() if n <= N})
    if cl.effective:
        def root_hits(N):
            try:
                return {n: pc.witnesses(n) for n in structural_hits(F, d, N)}
            except ValueError as exc:
                raise NotEnumerable(f'{CLASSIFIED_FINITE}: {exc}') from exc
        return dict(method=f'exact root reduction {strategy[:2]}', status=CLASSIFIED_FINITE,
                    justification=['Siegel via Theorem G (finite)', 'atlas structural_hits (Python)'],
                    data=base, hits=root_hits)
    return dict(method='finite by Siegel (Theorem G); no effective enumeration here',
                status=NOT_ENUMERATED, justification=['Siegel via Theorem G (paper; not in Lean)'],
                data={**base, 'curve': cl.curve, 'missing_premise': missing_premise(F, d)},
                hits=None)


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


def _root_params(con):
    """(a, b, c, F, L) of a quadratic-root form, or None; L = None for y in Z, else y >= L."""
    if isinstance(con, TriangularConstraint):
        a, b, c, F, dom = 1, 1, 0, pscale(con.F, 2), con.y_domain
    elif isinstance(con, QuadraticRootConstraint):
        a, b, c, F, dom = con.a, con.b, con.c, con.F, con.y_domain
    else:
        return None
    return a, b, c, _trim(F), {'int': None, 'nonneg': 0, 'pos': 1}[dom]


def _thr(a: int, b: int, L) -> int:
    """Past this |m|, the domain of y = (s|m| - b)/2a is the sign condition s = sign a
    (`FilteredPell.thr`)."""
    return 0 if L is None else abs(b) + 2 * abs(a) * (abs(L) + 1) + 1


def decide_filter(con, reduced: PowerConstraint) -> dict | None:
    """Decide a nontrivial admissibility filter on a reduced square family m^2 = G(n).

    Pell (G quadratic, A > 0 not a square): the unit acts on (X, Y) mod M = |4Aa| as a
    permutation; each seed orbit is a cycle; a state is admissible when 2A | X - B and
    2a | s Y - b for an admissible sign s.  Infinite iff some cycle meets an admissible state
    (Lean: FilteredPell.quadRoot_infinite_iff); otherwise every hit has |m| < thr, a complete
    finite search (FilteredPell.finite_bound).  kappa counts orbit indices, i.e. pairs (X, Y>=0),
    and X determines n, so no hit is counted twice.

    Radical (G = alpha n + beta, alpha > 0): m ranges over residues mod M = |2a alpha| with
    m^2 = beta (mod alpha); the same argument, by elementary periodicity (Python only).
    """
    rp = _root_params(con)
    if rp is None or reduced.d != 2:
        return None
    a, b, c, F, L = rp
    G = _trim(reduced.F)
    T = _thr(a, b, L)
    sgn = [1, -1] if L is None else [1 if a > 0 else -1]

    def adm_y(m_abs_mod: int, mod: int) -> bool:
        return any((s * m_abs_mod - b) % (2 * a) == 0 for s in sgn)
    if len(G) == 3 and G[2] > 0 and not is_square(G[2]) and G[1] ** 2 - 4 * G[2] * G[0]:
        C_, B_, A_ = G
        br = pell_branch(A_, B_, C_)
        M = abs(4 * A_ * a)
        x1, y1 = br.unit
        D = br.D
        cycles, g_total, witness = [], Fraction(0), None
        for X0, Y0 in br.seeds:
            st0 = (X0 % M, Y0 % M)
            st, j, marked = st0, 0, []
            while True:
                if (st[0] - B_) % (2 * A_) == 0 and adm_y(st[1], M):
                    marked.append(j)
                j += 1
                st = ((st[0] * x1 + D * st[1] * y1) % M, (st[0] * y1 + st[1] * x1) % M)
                if st == st0:
                    break
            cycles.append({'seed': [X0, Y0], 'period': j, 'marked': marked})
            g_total += Fraction(len(marked), j)
            if marked and witness is None:
                X, Y = X0, Y0
                for _ in range(marked[0]):
                    X, Y = X * x1 + D * Y * y1, X * y1 + Y * x1
                # whole periods keep the residue class; move into the quadrant X > 0, Y >= 0
                while X <= 0 or Y < 0:
                    for _ in range(j):
                        X, Y = X * x1 + D * Y * y1, X * y1 + Y * x1
                witness = [X, Y]
        log_eps = log(x1 + y1 * sqrt(D)) if x1 < 10 ** 15 else log(2 * x1)
        cert = {'kind': 'filtered_pell', 'modulus': M, 'D': D, 'Delta': br.Delta,
                'reduced_quadratic': [A_, B_, C_], 'unit': [x1, y1],
                'transition': f'(x, y) -> ({x1}x + {D * y1}y, {y1}x + {x1}y) mod {M}',
                'admissible': f'{2 * A_} | x - ({B_}) and {2 * a} | s*y - ({b}) for s in {sgn}',
                'threshold_T': T, 'cycles': cycles, 'witness': witness,
                'kappa': float(g_total) / log_eps if g_total else 0.0,
                'good_fraction': str(g_total)}
        if witness is not None:
            return {'infinite': True, 'certificate': cert,
                    'justification': ['PerfectPower.FilteredPell.quadRoot_infinite_iff',
                                      'PerfectPower.FilteredPell.infinite_iff_root_state']}
        # finite: every hit past the vertex has |m| = Y < T, so X^2 < Delta + 4A T^2
        bound_sq = br.Delta + 4 * A_ * T * T
        nmax = br.small_n()
        if bound_sq > 0:
            nmax = max(nmax, (isqrt(bound_sq) - B_) // (2 * A_) + 1)
        # the Lean certificate needs the stronger residue statement of finite_bound
        hno = not any((x * x - D * y * y - br.Delta) % M == 0 and (x - B_) % (2 * A_) == 0
                      and adm_y(y, M) for x in range(M) for y in range(M)) if M <= 3000 else None
        cert.update(search_bound_n=nmax, residue_certificate=hno)
        return {'infinite': False, 'nmax': nmax, 'certificate': cert,
                'justification': ['PerfectPower.FilteredPell.infinite_iff_root_state',
                                  'PerfectPower.FilteredPell.finite_bound']}
    if len(G) == 2 and G[1] > 0:
        beta, alpha = G
        M = abs(2 * a * alpha)
        good = [r for r in range(M) if (r * r - beta) % alpha == 0 and adm_y(r, M)]
        cert = {'kind': 'filtered_radical', 'modulus': M, 'reduced': f'm^2 = {alpha}n + ({beta})',
                'good_residues_of_m': good, 'threshold_T': T}
        just = ['elementary periodicity of m mod |2a alpha| (Python; not in Lean)']
        if good:
            cert['kappa'] = len(good) / M * sqrt(alpha)
            return {'infinite': True, 'certificate': cert, 'justification': just}
        nmax = max(1, (T * T - beta) // alpha + 1)
        cert['search_bound_n'] = nmax
        return {'infinite': False, 'nmax': nmax, 'certificate': cert, 'justification': just}
    return None


def _root_box(Delta: int, D: int, u: int) -> int:
    """The least Ymax with |Delta| u^2 < D (Ymax + 1)^2: every root has Y <= Ymax."""
    Ymax = max(0, isqrt(abs(Delta) * u * u // D) - 1)
    while not abs(Delta) * u * u < D * (Ymax + 1) ** 2:
        Ymax += 1
    return Ymax


def fin_cert(con) -> dict | None:
    """The data of a FilteredPell.FinCert for a finite filtered Pell plan: Ymax with
    |Delta| u^2 < D (Ymax + 1)^2 (so every root has Y <= Ymax, `root_in_box`), every quadrant
    solution with Y <= Ymax, and the cycle length of each modulo M."""
    rp = _root_params(con)
    if rp is None:
        return None
    a, b, c, F, L = rp
    if len(F) != 3:
        return None
    C0, B0, A0 = F
    A_, B_, C_ = 4 * a * A0, 4 * a * B0, 4 * a * C0 + b * b - 4 * a * c
    if A_ <= 0 or is_square(A_) or B_ * B_ - 4 * A_ * C_ == 0:
        return None
    D, Delta = 4 * A_, B_ * B_ - 4 * A_ * C_
    u, v = pell_fundamental(D)
    M = abs(4 * A_ * a)
    Ymax = _root_box(Delta, D, u)
    if Ymax > 10 ** 5:
        return None
    roots = []
    for Y in range(Ymax + 1):
        t = Delta + D * Y * Y
        if t > 0 and is_square(t):
            X = isqrt(t)
            st0 = (X % M, Y % M)
            st, k = st0, 0
            while True:
                st = ((st[0] * u + D * st[1] * v) % M, (st[0] * v + st[1] * u) % M)
                k += 1
                if st == st0:
                    break
            roots.append(((X, Y), k))
    return {'a': a, 'b': b, 'c': c, 'A0': A0, 'B0': B0, 'C0': C0, 'L': L, 'u': u, 'v': v,
            'M': M, 'Ymax': Ymax, 'roots': roots}


def count_cert(con) -> dict | None:
    """The data of a FilteredPell.CountCert: the exact roots (quadrant solutions whose predecessor
    is not one) in the box 4A Y^2 <= |Delta| u^2, each with its residue-cycle length P modulo
    M = |4Aa| and the number g of admissible states on the cycle.  Then
    kappa = (sum g / P) / log eps  (Lean: FilteredPell.quadRoot_count_of_cert)."""
    rp = _root_params(con)
    if rp is None:
        return None
    a, b, c, F, L = rp
    if len(F) != 3:
        return None
    C0, B0, A0 = F
    A_, B_, C_ = 4 * a * A0, 4 * a * B0, 4 * a * C0 + b * b - 4 * a * c
    if A_ <= 0 or is_square(A_) or B_ * B_ - 4 * A_ * C_ == 0:
        return None
    D, Delta = 4 * A_, B_ * B_ - 4 * A_ * C_
    u, v = pell_fundamental(D)
    M = abs(4 * A_ * a)
    Ymax = _root_box(Delta, D, u)
    if Ymax > 10 ** 5:
        return None
    sgn = [1, -1] if L is None else [1 if a > 0 else -1]

    def sol(X, Y):
        return X > 0 and Y >= 0 and X * X - D * Y * Y == Delta

    def goodB(X, Y):
        return (X - B_) % (2 * A_) == 0 and any((s * Y - b) % (2 * a) == 0 for s in sgn)
    isq, roots = [], []
    for Y in range(Ymax + 1):
        t = Delta + D * Y * Y
        q = isqrt(t) if t > 0 else 0
        isq.append(q)
        if t > 0 and q * q == t and q > 0:
            pX, pY = q * u - D * Y * v, u * Y - v * q
            if not sol(pX, pY):
                st0 = (q % M, Y % M)
                st, P, g = st0, 0, 0
                while True:
                    if goodB(*st):
                        g += 1
                    st = ((st[0] * u + D * st[1] * v) % M, (st[0] * v + st[1] * u) % M)
                    P += 1
                    if st == st0:
                        break
                roots.append(((q, Y), (P, g)))
    total = sum(Fraction(g, P) for _, (P, g) in roots)
    return {'a': a, 'b': b, 'c': c, 'A0': A0, 'B0': B0, 'C0': C0, 'L': L, 'u': u, 'v': v,
            'M': M, 'Ymax': Ymax, 'isqrts': isq, 'roots': roots, 'sum_g_over_P': total}


_PLAN_CERTS = None


def plan_certificate(con) -> list[str] | None:
    """The generated Lean theorem for this exact constraint (receipts/plan_certificates.json,
    written with PerfectPower/Generated/Plans.lean by python/make_lean_plans.py), or None."""
    global _PLAN_CERTS
    if _PLAN_CERTS is None:
        path = ROOT / 'receipts' / 'plan_certificates.json'
        try:
            _PLAN_CERTS = {r['constraint']: [r['theorem']] + r.get('also', [])
                           for r in json.loads(path.read_text())}
        except (OSError, ValueError):
            _PLAN_CERTS = {}
    return _PLAN_CERTS.get(con.describe())


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
    justification = [j for s in chain for j in s.lean] + solver['justification']
    data, hits, finite = solver['data'], solver['hits'], solver.get('finite')
    if status == STRUCTURED_FILTERED:
        dec = decide_filter(con, reduced)
        if dec is not None:
            data = {**data, 'filter_decision': dec['certificate']}
            justification += dec['justification']
            if dec['infinite']:
                status = STRUCTURED_INFINITE
            else:
                status = COMPLETE_FINITE
                finite = {n: w for n in range(1, dec['nmax'] + 1) if (w := reduced.witnesses(n))}
                hits = (lambda fin: lambda N: {n: w for n, w in fin.items() if n <= N})(finite)
    for cert in plan_certificate(con) or []:
        justification.append(f'{cert} (kernel-checked theorem for this plan)')
    return Plan(original=con, chain=chain, reduced=reduced, method=solver['method'],
                status=status, justification=justification,
                data=data, exact_to_any_N=hits is not None,
                _reduced_hits=hits, _reduced_contains=solver.get('contains'),
                _finite_list=finite)
