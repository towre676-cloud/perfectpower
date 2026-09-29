"""Structural classification of polynomial perfect-power hits ("the atlas").

For F in Z[x] and d >= 2 write F = c * prod_i (x - alpha_i)^(r_i) over the algebraic closure
and t_i = d / gcd(d, r_i).  y^d = F(x) has only finitely many integer solutions unless the multiset
{t_i} is {1, ..., 1}, {t, 1, ..., 1} or {2, 2, 1, ..., 1}: Theorem G of the research notes derives
this from Siegel's theorem via chi = d'(1 - S) (LeVeque 1964 found the same exceptional patterns).
The multiplicities are read off from an exact squarefree decomposition, so the type is
decidable.  In each exceptional type the hit set has an explicit description (Theorems B, C in
docs/RESEARCH_NOTES.md), which this module turns into exact enumeration and counting.

Kinds returned by classify():
  'constant'       deg F <= 0.
  'power'          every t_i = 1: F = c G^d with G monic in Q[x].  Density one iff c is an
                   integer d-th power; otherwise hits are exactly the positive integer roots of F.
  'radical'        {t, 1, ..., 1}, t >= 2: one rational root alpha carries the obstruction.
                   A(N) = kappa N^(1/t) + O(1) with an explicit kappa >= 0.
  'pell'           {2, 2, 1, ..., 1} (d even): reduces to squares of integer quadratics.
                   A(N) = kappa log N + O(1) with an explicit kappa >= 0.
  'finite'         anything else: finitely many hits (Siegel via Theorem G; historically LeVeque).  Enumerated effectively when
                   F is Runge-rigid for some divisor d' >= 2 of d (runge.runge_enumerate).
"""
from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from math import exp, gcd, isfinite, isqrt, log, log1p

from .arith import factorint, generalized_pell_classes, is_square, pell_fundamental, divisors
from .core import evaluate, integer_power_root, mul, normalize, power
from .polyalg import (ONE, degree, integer_roots, is_zero, poly, squarefree_decomposition)


@dataclass
class Classification:
    coefficients: tuple[int, ...]
    d: int
    kind: str
    leading: int
    multiplicity_profile: dict[int, int]      # root multiplicity j -> number of roots with it
    t_profile: dict[int, int]                 # t -> number of roots with that t
    growth: str                               # 'N', 'N^(1/t)', 'log N', 'bounded'
    exponent: Fraction                        # alpha = limsup log(1 + A(N)) / log N
    infinite: bool | None                     # None: not decided by this module
    effective: bool                           # complete hit list computable by this module
    details: dict = field(default_factory=dict)
    curve: dict = field(default_factory=dict)             # genus, points at infinity, chi (Theorem G)


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def integerize(coefficients, d: int) -> tuple[int, ...]:
    """Integer polynomial with the same hit set as an integer-valued F in Q[x].

    If F takes integer values on Z and L is the common denominator of its coefficients, then
    F(n) = m^d  <=>  L^d F(n) = (L m)^d, and conversely M^d = L^d F(n) makes F(n) = (M/L)^d
    an integer that is a rational d-th power, hence an integer d-th power.  So L^d F has
    exactly the same hits.  Raises ValueError if F is not integer-valued.
    """
    f = normalize(coefficients)
    if all(c.denominator == 1 for c in f):
        return tuple(int(c) for c in f)
    # integer-valued iff integral at deg F + 1 consecutive integers
    if any(evaluate(f, n).denominator != 1 for n in range(len(f))):
        raise ValueError('F must be integer-valued on the integers')
    L = 1
    for c in f:
        L = L * c.denominator // gcd(L, c.denominator)
    return tuple(int(c * L ** d) for c in f)


def _int_poly(coefficients) -> tuple[int, ...]:
    f = normalize(coefficients)
    if any(c.denominator != 1 for c in f):
        raise ValueError('F must have integer coefficients (use integerize for Q[x] input)')
    return tuple(int(c) for c in f)


def _eval_int(f, n: int) -> int:
    v = 0
    for c in reversed(f):
        v = v * n + c
    return v


def _positive_zeros(f, N: int | None = None) -> list[int]:
    if all(c == 0 for c in f):
        raise ValueError('zero polynomial')
    return integer_roots(f, lo=1, hi=N)


def _rational_power_root(c: Fraction, e: int) -> list[Fraction]:
    """All rational gamma with gamma^e = c (c != 0)."""
    if e == 1:
        return [c]
    num = integer_power_root(c.numerator, e) if c.numerator > 0 or e % 2 else None
    den = integer_power_root(c.denominator, e)
    if c.numerator < 0 and e % 2 == 0:
        return []
    if num is None or den is None:
        return []
    g = Fraction(num, den)
    return [g, -g] if e % 2 == 0 else [g]


# ---------------------------------------------------------------------------
# geometry of y^d = F(x)  (research notes, Theorem G)
# ---------------------------------------------------------------------------

def curve_invariants(F, d: int, parts: dict) -> dict:
    """Components, genus and points at infinity of the smooth models of y^d = F(x).

    With g = gcd(d, all multiplicities) the curve splits over Qbar into g components
    y^(d') = zeta c' prod (x - alpha_i)^(r_i / g), d' = d / g, each a cyclic cover of P^1 of
    degree d' with d'/t_i points over alpha_i and n_inf = gcd(d', deg F / g) points over infinity.
    Riemann-Hurwitz gives chi = 2 - 2 genus - n_inf = d' (1 - S), S = sum_i (1 - 1/t_i).
    """
    from functools import reduce
    g = reduce(gcd, [d] + list(parts))
    dp = d // g
    S = sum(Fraction(degree(s)) * (1 - Fraction(1, d // gcd(d, j))) for j, s in parts.items())
    n_inf = gcd(dp, degree(F) // g)
    chi = dp * (1 - S)
    genus = (2 - n_inf - chi) / 2
    assert genus.denominator == 1 and genus >= 0
    return {'components_over_Qbar': g, 'cover_degree': dp, 'S': str(S),
            'points_at_infinity': n_inf, 'genus': int(genus), 'euler_characteristic': str(chi),
            'siegel_finite': bool(chi < 0)}


# ---------------------------------------------------------------------------
# classification
# ---------------------------------------------------------------------------

def classify(coefficients, d: int) -> Classification:
    if d < 2:
        raise ValueError('d >= 2 required')
    f = _int_poly(coefficients)
    F = poly(f)
    if degree(F) <= 0:
        v = f[0]
        hit = integer_power_root(v, d) is not None
        return Classification(f, d, 'constant', v, {}, {}, 'N' if hit else 'bounded',
                              Fraction(1 if hit else 0), hit, True,
                              {'every_n_is_hit': hit})
    c, parts = squarefree_decomposition(F)
    lead = int(c)
    mult = {j: degree(s) for j, s in parts.items()}
    tprof: dict[int, int] = {}
    for j, k in mult.items():
        t = d // gcd(d, j)
        tprof[t] = tprof.get(t, 0) + k
    special = {t: k for t, k in tprof.items() if t != 1}
    nspecial = sum(special.values())
    base = dict(coefficients=f, d=d, leading=lead, multiplicity_profile=mult,
                t_profile=dict(sorted(tprof.items())), curve=curve_invariants(F, d, parts))

    if nspecial == 0:
        G = ONE
        for j, s in parts.items():
            G = mul(G, power(s, j // d))
        b = integer_power_root(lead, d)
        if b is not None:
            return Classification(kind='power', growth='N', exponent=Fraction(1), infinite=True,
                                  effective=True, details={'root_leading': b,
                                  'G_monic_rational': [str(x) for x in G]}, **base)
        return Classification(kind='power', growth='bounded', exponent=Fraction(0),
                              infinite=False, effective=True,
                              details={'twist_not_dth_power': lead,
                                       'G_monic_rational': [str(x) for x in G]}, **base)

    if nspecial == 1:
        (t,) = special
        (j0,) = [j for j in parts if d // gcd(d, j) != 1]
        alpha = -parts[j0][0]
        info = _radical_data(f, d, lead, alpha, j0)
        # The numerical approximation to κ may underflow for large squarefree twists.
        # A positive admissible residue class is the exact infinitude criterion.
        infinite = bool(info['good_residues_mod_v'])
        return Classification(kind='radical', growth=f'N^(1/{t})' if infinite else 'bounded',
                              exponent=Fraction(1, t) if infinite else Fraction(0),
                              infinite=infinite, effective=True, details=info, **base)

    if nspecial == 2 and set(special) == {2}:
        js = [j for j in parts if d // gcd(d, j) == 2]
        W = ONE
        for j in js:
            W = mul(W, parts[j])
        info = _pell_data(f, d, lead, W)
        # Each quadratic's good_fraction is an exact rational number.  A tiny
        # positive coefficient can round to 0.0 in the displayed approximation.
        infinite = any(Fraction(q['good_fraction']) > 0 for q in info['quadratics']
                       if q['case'] == 'pell')
        return Classification(kind='pell', growth='log N' if infinite else 'bounded',
                              exponent=Fraction(0), infinite=infinite, effective=True,
                              details=info, **base)

    # Hits for d are hits for every divisor d' of d, so a Runge-rigid divisor d' >= 2
    # (d' | deg F and lead(F) an integer d'-th power) makes the finite hit set computable.
    strategy = _finite_strategy(f, d)
    return Classification(kind='finite', growth='bounded', exponent=Fraction(0), infinite=False,
                          effective=strategy is not None,
                          details={'theorem': 'Siegel via Theorem G (chi = d\'(1 - S) < 0); historically LeVeque 1964; effective by Brindza 1984',
                                   'rigid_runge_branch': strategy is not None and strategy[0] == 'runge'
                                   and strategy[1] == d,
                                   'strategy': strategy}, **base)


def _exact_root(f, e: int):
    """G in Z[x] with G^e = f (leading coefficient positive when e is even), or None."""
    from .core import rigid_certificate
    if len(f) - 1 < 1 or (len(f) - 1) % e or integer_power_root(f[-1], e) is None:
        return None
    cert = rigid_certificate(f, e)
    if cert is None or not cert.exact_identity:
        return None
    return tuple(cert.root_numerators)


def _finite_strategy(f, d: int):
    """How to enumerate the (finite) hit set of (f, d) effectively, or None.

    ('runge', e): f is Runge-rigid for the divisor e >= 2 of d and not an exact e-th power;
                  hits for d are the hits for e that are also d-th powers.
    ('root', e, G): f = G^e exactly for a divisor e of d with 2 <= e < d; then f(n) = m^d iff
                  G(n) = s^(d/e) (odd e), or G(n) = +-s^(d/e) (even e).
    """
    deg = len(f) - 1
    for e in sorted((e for e in range(2, d + 1) if d % e == 0), reverse=True):
        if deg % e or integer_power_root(f[-1], e) is None:
            continue
        G = _exact_root(f, e)
        if G is None:
            return ('runge', e)
    for e in sorted((e for e in range(2, d) if d % e == 0), reverse=True):
        G = _exact_root(f, e)
        if G is not None:
            sub = [G] + ([tuple(-c for c in G)] if e % 2 == 0 else [])
            if all(classify(g, d // e).effective for g in sub):
                return ('root', e, G)
    return None


# ---------------------------------------------------------------------------
# radical type:  F = c (x - alpha)^r G^d,  t = d / gcd(d, r) >= 2
# ---------------------------------------------------------------------------

def _radical_data(f, d: int, c: int, alpha: Fraction, r: int) -> dict:
    u, v = alpha.numerator, alpha.denominator          # alpha = u / v, v >= 1
    K = -(-r // d)
    c1 = c * v ** (d * K - r)                           # c (z/v)^r in Q^d  <=>  c1 z^r in Z^d
    g = gcd(r, d)
    t, r1 = d // g, r // g
    fac = factorint(c1)
    solvable = all(e % g == 0 for e in fac.values())
    z0 = 1
    if solvable:
        inv = pow(r1, -1, t) if t > 1 else 0
        for p, e in fac.items():
            z0 *= p ** ((-(e // g) * inv) % t)
    if d % 2:
        signs = [1, -1]
    else:
        signs = [s for s in (1, -1) if c1 * s ** r > 0]
    if not solvable:
        signs = []
    good = sorted(w for w in range(v) if (z0 * w ** t + u) % v == 0) if 1 in signs else []
    kappa = Fraction(len(good), v)                      # times (v / z0)^(1/t): see count
    try:
        kappa_float = float(kappa) * (v / z0) ** (1 / t) if good else 0.0
    except OverflowError:
        kappa_float = None
    if good and (kappa_float is None or not isfinite(kappa_float) or kappa_float == 0.0):
        # Retain the exact expression in JSON; null means the approximation is
        # below float range, not that the constant is zero.
        kappa_float = None
    return {'alpha': str(alpha), 'r': r, 't': t, 'c1': c1, 'solvable': solvable, 'z0': z0,
            'signs': signs, 'good_residues_mod_v': good, 'v': v, 'u': u,
            'kappa': kappa_float,
            **({'kappa_exact': {'coefficient': str(kappa), 'radicand_num': v,
                                'radicand_den': z0, 'degree': t}}
               if good and kappa_float is None else {}),
            'formula': 'hits = zeros of F  U  {(s z0 w^t + u)/v : w >= 1, s in signs, integral, >= 1}'}


def _radical_param_hits(info: dict, N: int) -> set[int]:
    z0, t, u, v = info['z0'], info['t'], info['u'], info['v']
    out = set()
    for s in info['signs']:
        if s > 0:
            # z = z0 w^t with w in a good class mod v; stop once n = (z + u)/v exceeds N
            for rho in info['good_residues_mod_v']:
                w = rho if rho >= 1 else v
                while z0 * w ** t + u <= v * N:
                    n_num = z0 * w ** t + u
                    if n_num >= v:
                        out.add(n_num // v)
                    w += v
        else:
            w = 1
            while u - z0 * w ** t >= v:        # n = (u - z0 w^t)/v >= 1
                n_num = u - z0 * w ** t
                if n_num % v == 0 and n_num // v <= N:
                    out.add(n_num // v)
                w += 1
    return out


def _radical_param_count(info: dict, N: int) -> int:
    """Exact count of parametrized hits in [1, N] without listing them."""
    z0, t, u, v = info['z0'], info['t'], info['u'], info['v']
    total = 0
    for s in info['signs']:
        if s > 0:
            # w >= 1 with v <= z0 w^t + u <= v N and w in a good residue class mod v
            hi_val = v * N - u
            if hi_val < z0:
                continue
            wmax = _floor_root(hi_val // z0, t)
            lo_val = v - u
            wmin = 1 if lo_val <= z0 else _ceil_root(-(-lo_val // z0), t)
            for rho in info['good_residues_mod_v']:
                total += _count_in_class(wmin, wmax, rho, v)
        else:
            total += sum(1 for n in _radical_param_hits({**info, 'signs': [-1]}, N))
    return total


def _floor_root(x: int, t: int) -> int:
    if x <= 0:
        return 0
    r = integer_power_root(x, t)
    if r is not None:
        return r
    lo, hi = 0, 1
    while hi ** t <= x:
        hi *= 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** t <= x:
            lo = mid
        else:
            hi = mid
    return lo


def _ceil_root(x: int, t: int) -> int:
    r = _floor_root(x, t)
    return r if r ** t >= x else r + 1


def _count_in_class(lo: int, hi: int, rho: int, v: int) -> int:
    if hi < lo:
        return 0
    first = lo + ((rho - lo) % v)
    return 0 if first > hi else (hi - first) // v + 1


# ---------------------------------------------------------------------------
# Pell type:  F = c W^e H^d,  d = 2e,  W monic quadratic with distinct roots
# ---------------------------------------------------------------------------

def _pell_data(f, d: int, c: int, W) -> dict:
    e = d // 2
    gammas = _rational_power_root(Fraction(c), e)
    L = 1
    for x in W:
        L = L * x.denominator // gcd(L, x.denominator)
    LW = [int(x * L) for x in W]                        # integer quadratic L*W
    quads = []
    kappa = 0.0
    for gam in gammas:
        g1, g2 = gam.numerator, gam.denominator
        k = g1 * g2 * L
        A, B, C = (k * LW[2], k * LW[1], k * LW[0])
        qd = quadratic_square_data(A, B, C)
        quads.append(qd)
        if qd['kappa'] is None:
            kappa = None
        elif kappa is not None:
            kappa += qd['kappa']
    positive = any(Fraction(q['good_fraction']) > 0 for q in quads if q['case'] == 'pell')
    if positive and kappa == 0.0:
        kappa = None
    return {'W': [str(x) for x in W], 'gammas': [str(g) for g in gammas],
            'quadratics': quads, 'kappa': kappa,
            **({'kappa_exact': [{'good_fraction': q['good_fraction'], 'unit': q['unit'],
                                 'D': q['D']} for q in quads if q['case'] == 'pell']}
               if positive and kappa is None else {}),
            'formula': 'hits = zeros of F  U  {n : A n^2 + B n + C is a square} over the quadratics'}


def quadratic_square_data(A: int, B: int, C: int) -> dict:
    """Asymptotic data for #{1 <= n <= N : A n^2 + B n + C = m^2}, disc != 0, A != 0."""
    Delta = B * B - 4 * A * C
    if A == 0 or Delta == 0:
        raise ValueError('need a genuine quadratic with nonzero discriminant')
    out = {'A': A, 'B': B, 'C': C, 'Delta': Delta}
    if A < 0:
        out.update(case='ellipse', kappa=0.0)
    elif is_square(A):
        out.update(case='split', kappa=0.0)
    else:
        Dp = 4 * A
        x1, y1 = pell_fundamental(Dp)
        # Avoid converting a potentially huge discriminant or unit to float.
        # The ratio in exp(...) is strictly below 1 by the Pell identity.
        log_eps = log(x1) + log1p(exp(log(y1) + log(Dp) / 2 - log(x1)))
        g_over_pi = Fraction(0)
        orbits = _positive_orbits(Dp, Delta)
        for (X, Y) in orbits:
            # iterate (X, Y) -> (X x1 + Dp Y y1, X y1 + Y x1) modulo 2A until the state repeats
            M = 2 * A
            state0 = (X % M, Y % M)
            state, period, good = state0, 0, 0
            while True:
                if state[0] == B % M:
                    good += 1
                period += 1
                state = ((state[0] * x1 + Dp * state[1] * y1) % M, (state[0] * y1 + state[1] * x1) % M)
                if state == state0:
                    break
            g_over_pi += Fraction(good, period)
        kappa = float(g_over_pi) / log_eps
        out.update(case='pell', D=Dp, unit=(x1, y1), orbits=orbits,
                   good_fraction=str(g_over_pi),
                   kappa=None if g_over_pi > 0 and kappa == 0.0 else kappa)
    return out


def _positive_orbits(Dp: int, M: int) -> list[tuple[int, int]]:
    """Canonical representatives of the orbits of positive eta = X + Y sqrt(Dp) of norm M
    under multiplication by the fundamental unit eps = x1 + y1 sqrt(Dp)."""
    x1, y1 = pell_fundamental(Dp)
    reps = set()
    for x0, y0 in generalized_pell_classes(Dp, M):
        for X, Y in ((x0, y0), (-x0, -y0), (x0, -y0), (-x0, y0)):
            # keep eta > 0:  X + Y sqrt(Dp) > 0
            if not _eta_positive(X, Y, Dp):
                continue
            reps.add(_canonical(X, Y, Dp, x1, y1))
    return sorted(reps)


def _eta_positive(X: int, Y: int, Dp: int) -> bool:
    if X >= 0 and Y >= 0:
        return X > 0 or Y > 0
    if X <= 0 and Y <= 0:
        return False
    if X > 0:                     # Y < 0: X > |Y| sqrt(Dp)
        return X * X > Dp * Y * Y
    return Dp * Y * Y > X * X     # X < 0 < Y


def _canonical(X: int, Y: int, Dp: int, x1: int, y1: int) -> tuple[int, int]:
    """Orbit element of eta = X + Y sqrt(Dp) > 0 with Y >= 0 minimal, ties broken by X."""
    def up(X, Y):
        return X * x1 + Dp * Y * y1, X * y1 + Y * x1

    def down(X, Y):
        return X * x1 - Dp * Y * y1, -X * y1 + Y * x1
    # move so that Y > 0 (eta large enough), then descend while Y stays >= 0 and decreases
    while Y <= 0:
        X, Y = up(X, Y)
    # |Y_k| is decreasing-then-increasing along the orbit, so descend while Y stays >= 0
    # and does not grow; for norm M < 0 every positive eta has Y > 0 and Y has a minimum.
    while True:
        nX, nY = up(X, Y)
        if nY >= Y:
            break
        X, Y = nX, nY
    best = (Y, X)
    seen = {(X, Y)}
    while True:
        nX, nY = down(X, Y)
        if nY < 0 or nY > Y or (nX, nY) in seen:
            break
        X, Y = nX, nY
        seen.add((X, Y))
        best = min(best, (Y, X))
    return best[1], best[0]


def quadratic_square_hits(A: int, B: int, C: int, N: int) -> set[int]:
    """Exact {1 <= n <= N : A n^2 + B n + C is a perfect square}, disc != 0, A != 0."""
    Delta = B * B - 4 * A * C
    out = set()
    if A < 0:
        # P(n) >= 0 forces (2 A n + B)^2 <= Delta, so n <= (isqrt(Delta) + 1 + |B|) / (2|A|)
        if Delta < 0:
            return out
        nmax = (isqrt(Delta) + 1 + abs(B)) // (2 * -A) + 1
        for n in range(1, min(N, nmax) + 1):
            v = A * n * n + B * n + C
            if v >= 0 and is_square(v):
                out.add(n)
        return out
    if is_square(A):
        s = isqrt(A)
        # (X - 2 s m)(X + 2 s m) = Delta with X = 2 A n + B
        for dv in divisors(Delta):
            for d1 in (dv, -dv):
                d2 = Delta // d1
                if (d1 + d2) % 2:
                    continue
                X = (d1 + d2) // 2
                if (X - B) % (2 * A) == 0:
                    n = (X - B) // (2 * A)
                    if 1 <= n <= N and is_square(A * n * n + B * n + C):
                        out.add(n)
        return out
    from .arith import generalized_pell_solutions
    for X, Y in generalized_pell_solutions(4 * A, Delta, 2 * A * N + abs(B)):
        if (X - B) % (2 * A) == 0:
            n = (X - B) // (2 * A)
            if 1 <= n <= N:
                out.add(n)
    return out


# ---------------------------------------------------------------------------
# structural enumeration
# ---------------------------------------------------------------------------

def structural_hits(coefficients, d: int, N: int) -> list[int]:
    """All hits 1 <= n <= N computed from the classification (never by scanning n), except in
    the 'finite' kind, where the rigid sub-branch uses the Runge enumeration and the nonrigid
    sub-branch raises NotImplementedError."""
    cl = classify(coefficients, d)
    f = cl.coefficients
    if cl.kind == 'constant':
        return list(range(1, N + 1)) if cl.infinite else []
    if cl.kind == 'power':
        if cl.infinite:
            return list(range(1, N + 1))
        return _positive_zeros(f, N)
    zeros = set(_positive_zeros(f, N))
    if cl.kind == 'radical':
        return sorted(zeros | _radical_param_hits(cl.details, N))
    if cl.kind == 'pell':
        hits = set(zeros)
        for q in cl.details['quadratics']:
            hits |= quadratic_square_hits(q['A'], q['B'], q['C'], N)
        return sorted(hits)
    if cl.effective:
        strategy = cl.details['strategy']
        if strategy[0] == 'runge':
            from .runge import runge_enumerate
            e = strategy[1]
            return [n for n, _ in runge_enumerate(f, e).hits
                    if n <= N and integer_power_root(_eval_int(f, n), d) is not None]
        _, e, G = strategy
        cand = set(structural_hits(G, d // e, N))
        if e % 2 == 0:
            cand |= set(structural_hits(tuple(-c for c in G), d // e, N))
        return sorted(n for n in cand if integer_power_root(_eval_int(f, n), d) is not None)
    raise NotImplementedError('finite by Siegel (Theorem G), but no effective enumeration implemented')


def structural_count(coefficients, d: int, N: int) -> int:
    """Exact A(N); for the radical kind this is O(v) work independent of N."""
    cl = classify(coefficients, d)
    if cl.kind == 'radical':
        f = cl.coefficients
        zeros = _positive_zeros(f, N)
        info = cl.details
        param = _radical_param_count(info, N)
        extra = 0
        for n in zeros:
            if n not in _radical_param_hits_single(info, n):
                extra += 1
        return param + extra
    if cl.kind in ('constant', 'power') and cl.infinite:
        return N
    return len(structural_hits(coefficients, d, N))


def _radical_param_hits_single(info: dict, n: int) -> set[int]:
    z = info['v'] * n - info['u']
    if z == 0:
        return set()
    s = 1 if z > 0 else -1
    if s not in info['signs'] or abs(z) % info['z0']:
        return set()
    w = integer_power_root(abs(z) // info['z0'], info['t'])
    return {n} if w is not None and w >= 1 else set()


# ---------------------------------------------------------------------------
# shift spectrum: how the type of S + k depends on the integer shift k
# ---------------------------------------------------------------------------

def critical_shifts(S) -> list[int]:
    """Integers k for which S + k has a repeated root, i.e. k = -S(xi) with S'(xi) = 0.

    These are the integer roots of R(k) = Res_x(S(x) + k, S'(x)), a polynomial in k of degree
    deg S - 1, recovered exactly by interpolation.
    """
    from .polyalg import derivative, interpolate, resultant
    s = poly(_int_poly(S))
    m = degree(s)
    if m < 2:
        return []
    ds = derivative(s)
    xs = list(range(m))
    ys = [resultant(poly((s[0] + k,) + tuple(s[1:])), ds) for k in xs]
    return integer_roots(interpolate(xs, ys))


def shift_spectrum(S, d: int) -> dict:
    """Type of S + k for every integer k.

    Outside the finite set critical_shifts(S), S + k is squarefree, so every root has
    t = d and the type depends only on deg S and d:
      deg S = 1 -> radical (t = d);  deg S = 2, d = 2 -> Pell;  otherwise -> finite (Siegel via Theorem G).
    At most one k makes S + k an integer-polynomial d-th power.
    """
    s = _int_poly(S)
    m = len(s) - 1
    if m < 1:
        raise ValueError('S must be nonconstant')
    generic = 'radical' if m == 1 else ('pell' if (m == 2 and d == 2) else 'finite')
    special = {}
    for k in critical_shifts(s):
        f = list(s)
        f[0] += k
        cl = classify(f, d)
        special[k] = {'kind': cl.kind, 'growth': cl.growth, 'exponent': str(cl.exponent),
                      't_profile': cl.t_profile}
    return {'S': s, 'd': d, 'generic_kind': generic, 'critical_shifts': special}
