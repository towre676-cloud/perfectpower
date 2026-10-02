"""Positive `k`: `y² = x³ + k` through Mordell's cubic forms (`receipts/positive_k.json`).

The negative-`k` branch compiler factors `y² + D` in the imaginary quadratic order `ℤ[√−D]`.  For
`k > 0` the same factorization is real quadratic, with an infinite unit group (`MORDELL_BRANCH.md`
§7.4).  This module takes the other classical route (Mordell, *Diophantine Equations*, ch. 24),
which needs no quadratic field at all:

* **Forward** (`PerfectPower/MordellCubicForm.lean`, `form_of_point`).  If `y² = x³ + k`, then
  `F = X³ − 3x XY² − 2y Y³ = (1, 0, −3x, −2y)` has `F(1, 0) = 1` and discriminant `−108k`.
  Writing forms as `(a, 3b, 3c, d)`, the invariant is
  `Δ = (ad − bc)² − 4(ac − b²)(bd − c²) = 4k`, and `disc = −27Δ`.
* **Back** (`point_of_form`).  If `G` has the shape `(a, 3b, 3c, d)` with `Δ = 4k` and `G(u, v) = 1`
  with `gcd(u, v) = 1`, complete `(u, v)` to `T ∈ SL₂(ℤ)` and shift `X ↦ X − b'Y`.  The result is
  `(1, 0, 3c'', d'')` with `d''² + 4c''³ = 4k`, so `x = −c''` and `y = −d''/2` is a point.
* **Finiteness.**  `GL₂(ℤ)` preserves the shape and `Δ`, and there are finitely many classes.  So
  the curve is the union, over the classes, of the Thue equations `G = 1`.  Since `disc < 0`,
  each lies in a complex cubic field, with unit rank 1 (one unit, not two as for negative `k`).

**Canonical forms.**  The Hessian is indefinite when `disc < 0`, so `thue_graph.canonical`
(Gauss reduction of the Hessian) does not apply.  Instead we use the covariant quadratic
`q = (X − ρY)²/F'(ρ)² + 2|X − θY|²/|F'(θ)|²`, built from the real root `ρ` and a complex root `θ`.
It is positive definite and `q(F ∘ T) = q(F) ∘ T` for `T ∈ GL₂(ℤ)`.  It is computed in floating
point, and classes are then merged by explicit matrices (`F ∘ T = G`, exact).

**Evidence.**
* The class lists come from a coefficient search that grows until the set of classes stabilizes
  (`SEARCH_STABLE`). They are **not proved complete**: that needs a reduction bound, here or in
  Lean.
* "Locally impossible" (`G = 1` has no solution mod `m`) is exact.
* The points are matched against the independent census (`data/mordell_census.csv`).
* Nothing here is a Lean completeness theorem for positive `k`.

Run: python3 python/positive_k.py
"""
from __future__ import annotations

import cmath
import csv
import itertools
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower import thue_graph as TG  # noqa: E402


def delta(F):
    """`Δ` for `F = (a, 3b, 3c, d)`, or None if the middle coefficients are not divisible by 3."""
    a, B, C, d = F
    if B % 3 or C % 3:
        return None
    b, c = B // 3, C // 3
    return (a * d - b * c) ** 2 - 4 * (a * c - b * b) * (b * d - c * c)


def form_of_point(x, y):
    return (1, 0, -3 * x, -2 * y)


def point_of_rep(G, u, v):
    """The point read off from `G(u, v) = 1` (`G` of shape `(a, 3b, 3c, d)`)."""
    assert TG.evalF(G, u, v) == 1 and math.gcd(u, v) == 1
    g, s, t = _egcd(u, v)                         # s u + t v = 1
    T = ((u, -t), (v, s))                          # det = u s + t v = 1
    F = TG.compose(G, T)
    assert F[0] == 1 and F[1] % 3 == 0
    b = F[1] // 3
    F = TG.compose(F, ((1, -b), (0, 1)))
    assert F[0] == 1 and F[1] == 0 and F[2] % 3 == 0 and F[3] % 2 == 0
    return (-F[2] // 3, -F[3] // 2)


def _egcd(a, b):
    if b == 0:
        return (abs(a), (1 if a > 0 else -1), 0)
    g, x, y = _egcd(b, a % b)
    return g, y, x - (a // b) * y


# ---------------------------------------------------------------------------------- canonical forms

def _roots(F):
    """The real root (bisection, then Newton) and the complex pair (deflation) of `F(X, 1)`, `disc < 0`."""
    a, b, c, d = F
    f = lambda z: ((a * z + b) * z + c) * z + d                 # noqa: E731
    M = 1 + max(abs(b), abs(c), abs(d)) / abs(a)
    lo, hi = -M, M
    if f(lo) > 0:
        lo, hi = hi, lo
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid) < 0:
            lo = mid
        else:
            hi = mid
    r = (lo + hi) / 2
    # F(X, 1) = (X − r)(a X² + e X + g)
    e = b + a * r
    g = c + e * r
    sq = cmath.sqrt(e * e - 4 * a * g)
    return [complex(r, 0), (-e + sq) / (2 * a), (-e - sq) / (2 * a)]


def covariant_q(F):
    """The positive definite covariant quadratic `(A, B, C)` (floats); `F(1, 0) ≠ 0` required."""
    a, b, c, d = F
    rs = _roots(F)
    rho, theta = rs[0].real, max(rs[1:], key=lambda z: z.imag)
    dF = lambda z: 3 * a * z * z + 2 * b * z + c          # noqa: E731
    w1 = 1 / abs(dF(rho)) ** 2
    w2 = 2 / abs(dF(theta)) ** 2
    # w1 (X − ρY)² + w2 (X − θY)(X − θ̄Y)
    A = w1 + w2
    B = -2 * w1 * rho - 2 * w2 * theta.real
    C = w1 * rho * rho + w2 * abs(theta) ** 2
    return (A, B, C)


def _fcompose_q(q, T):
    return TG.qcompose(q, T)


def canonical(F, tol=1e-9):
    """(key, T): the least `F ∘ T` over the `T` that make `q(F) ∘ T` (nearly) reduced."""
    if F[0] == 0:                                   # move a nonzero value to the front
        for T0 in (((0, 1), (1, 0)), ((1, 1), (0, 1)), ((1, 0), (1, 1))):
            if TG.compose(F, T0)[0] != 0:
                k, T = canonical(TG.compose(F, T0), tol)
                return k, TG.matmul(T0, T)
    q = covariant_q(F)
    T = ((1, 0), (0, 1))
    A, B, C = q
    for _ in range(10000):
        if abs(B) > A * (1 + tol):
            n = -round(B / (2 * A))
            S = ((1, n), (0, 1))
        elif A > C * (1 + tol):
            S = ((0, -1), (1, 0))
        else:
            break
        A, B, C = _fcompose_q((A, B, C), S)
        T = TG.matmul(T, S)
    best = None
    for S in WIDE:
        A2, B2, C2 = _fcompose_q((A, B, C), S)
        if abs(B2) <= A2 * (1 + 1e-6) and A2 <= C2 * (1 + 1e-6):
            U = TG.matmul(T, S)
            G = TG.compose(F, U)
            if best is None or G < best[0]:
                best = (G, U)
    return best


WIDE = [((a, b), (c, d)) for a, b, c, d in itertools.product(range(-2, 3), repeat=4) if a * d - b * c in (1, -1)]


def equivalent(F, G, R=4):
    """An explicit `T` with `F ∘ T = G` (entries ≤ R), or None."""
    for a, b, c, d in itertools.product(range(-R, R + 1), repeat=4):
        if a * d - b * c in (1, -1) and TG.compose(F, ((a, b), (c, d))) == G:
            return ((a, b), (c, d))
    return None


# ---------------------------------------------------------------------------------- the class search

def forms_with_delta(k, R):
    """Forms `(a, 3b, 3c, d)` with `Δ = 4k`, `|a|, |b|, |c| ≤ R`, `d` solved from `Δ` (quadratic in d)."""
    out = []
    for a in range(1, R + 1):                     # F and −F: −F(u, v) = F(−u, −v), same class
        for b in range(-R, R + 1):
            for c in range(-R, R + 1):
                # Δ = a²d² + d(−2abc − 4a·... ) ... solve exactly: Δ(d) is quadratic in d
                # Δ = (ad − bc)² − 4(ac − b²)(bd − c²) = a²d² + d(−2abc − 4b(ac − b²)) + b²c² + 4c²(ac − b²)
                A2 = a * a
                B2 = -2 * a * b * c - 4 * b * (a * c - b * b)
                C2 = b * b * c * c + 4 * c * c * (a * c - b * b) - 4 * k
                disc = B2 * B2 - 4 * A2 * C2
                if disc < 0:
                    continue
                s = math.isqrt(disc)
                if s * s != disc:
                    continue
                for num in {-B2 + s, -B2 - s}:
                    if num % (2 * A2) == 0:
                        d = num // (2 * A2)
                        F = (a, 3 * b, 3 * c, d)
                        assert delta(F) == 4 * k
                        out.append(F)
    return out


def classes(k, R0=4, Rmax=40):
    """Grow the search box until the classes stop changing for two doublings."""
    reps, history, R = {}, [], R0
    while R <= Rmax:
        for F in forms_with_delta(k, R):
            if TG.disc(F) == 0:
                continue
            key, _ = canonical(F)
            if key in reps:
                continue
            if any(equivalent(key, G) for G in reps):
                continue
            reps[key] = F
        history.append((R, len(reps)))
        if len(history) >= 3 and history[-1][1] == history[-2][1] == history[-3][1]:
            break
        R *= 2
    return sorted(reps), history


def local_impossible(G, mods=(2, 3, 4, 5, 7, 8, 9, 13, 16, 19, 27, 37)):
    """The least `m` with `G(u, v) ≢ 1 (mod m)` for all `u, v`, or None."""
    for m in mods:
        if all((TG.evalF(G, u, v) - 1) % m for u in range(m) for v in range(m)):
            return m
    return None


def small_reps(G, R=60):
    return sorted((u, v) for u in range(-R, R + 1) for v in range(-R, R + 1)
                  if TG.evalF(G, u, v) == 1 and math.gcd(u, v) == 1)


def census_points():
    out = {}
    for row in csv.DictReader(open(ROOT / 'data' / 'mordell_census.csv')):
        k = int(row['k'])
        if 1 <= k <= 100:
            xs = [int(t) for t in row['x_coordinates'].split()]
            out[k] = {'rank': int(row['rank']),
                      'points': sorted((x, s * math.isqrt(x ** 3 + k)) for x in xs for s in (1, -1)
                                       if math.isqrt(x ** 3 + k) ** 2 == x ** 3 + k)}
            out[k]['points'] = sorted(set(out[k]['points']))
    return out


def run(K=100):
    cen = census_points()
    rows = []
    for k in range(1, K + 1):
        reps, hist = classes(k)
        cls = []
        for G in reps:
            m = local_impossible(G)
            sols = [] if m else small_reps(G)
            pts = sorted({p for (u, v) in sols for p in [point_of_rep(G, u, v)]})
            cls.append({'form': list(G), 'disc': TG.disc(G), 'local_obstruction': m,
                        'representations': sols, 'points': pts})
        found = sorted({tuple(p) for c in cls for p in c['points']}
                       | {(x, -y) for c in cls for (x, y) in c['points']})
        # every census point must come from some class (a check on the class search)
        missing = [p for p in cen[k]['points'] if not any(
            equivalent(canonical(form_of_point(*p))[0], tuple(c['form'])) or
            canonical(form_of_point(*p))[0] == tuple(c['form']) for c in cls)]
        open_classes = [c for c in cls if c['local_obstruction'] is None]
        rows.append({'k': k, 'rank': cen[k]['rank'], 'classes': len(cls), 'search': hist,
                     'locally_impossible': len(cls) - len(open_classes), 'open_thue': len(open_classes),
                     'open_with_points': sum(bool(c['points']) for c in open_classes),
                     'census_points': cen[k]['points'], 'points_found': found,
                     'agrees_with_census': found == cen[k]['points'], 'census_points_unmatched': missing,
                     'class_detail': cls})
        print(k, len(cls), len(open_classes), found == cen[k]['points'], missing, flush=True)
    summary = {
        'curves': len(rows),
        'classes': sum(r['classes'] for r in rows),
        'classes_locally_impossible': sum(r['locally_impossible'] for r in rows),
        'all_classes_locally_impossible': [r['k'] for r in rows if r['open_thue'] == 0],
        'open_thue_equations': sum(r['open_thue'] for r in rows),
        'open_with_points': sum(r['open_with_points'] for r in rows),
        'open_point_free': sum(r['open_thue'] - r['open_with_points'] for r in rows),
        'agree_with_census': sum(r['agrees_with_census'] for r in rows),
        'census_points_unmatched': sum(len(r['census_points_unmatched']) for r in rows),
    }
    out = {'label': 'Positive k through Mordell cubic forms: class search (NOT proved complete), exact '
                    'local obstructions, representations of 1 by search (|u|, |v| <= 60), census cross-check',
           'summary': summary, 'curves': rows}
    (ROOT / 'receipts' / 'positive_k.json').write_text(json.dumps(out, indent=1, default=list) + '\n')
    lean_module(rows)
    print(summary)
    return out


def _i(n):
    return f'({n})' if n < 0 else str(n)


def lean_module(rows):
    """`Generated/PositiveK.lean`: the curves all of whose classes are locally impossible, empty under
    the class-list premise (`MordellCubicForm.no_point_of_cert`)."""
    out = ['import PerfectPower.MordellCubicForm\n\n/-!\n# Positive `k`: curves `y² = x³ + k` with no integral point, '
           'under the class-list premise\n(generated by `python/positive_k.py`)\n\n'
           'Each `cs_k` lists the `GL₂(ℤ)` classes of forms `(a, 3b, 3c, d)` with `Δ = 4k` (stored as\n'
           '`(a, b, c, d)`) found by `python/positive_k.py`, each with a modulus `m` such that the form never\n'
           'takes the value `1` modulo `m`.  The kernel checks `Δ` and the residues (`emptyCertB`).  The\n'
           'premise `ClassList k` (that the list contains every class) is **not proved**: it is the hypothesis\n'
           'of each theorem.\n-/\n\nnamespace PerfectPower.Generated.PositiveK\n\nopen PerfectPower MordellCubicForm\n']
    for r in rows:
        if r['open_thue']:
            continue
        k = r['k']
        cs = []
        for c in r['class_detail']:
            a, B, C, d = c['form']
            cs.append(f"(({_i(a)}, {_i(B // 3)}, {_i(C // 3)}, {_i(d)}), {c['local_obstruction']})")
        out.append(f"/-- The {len(cs)} class(es) for `k = {k}`, each with a residue modulus. -/\n"
                   f"def cs_{k} : List ((ℤ × ℤ × ℤ × ℤ) × ℕ) := [{', '.join(cs)}]\n\n"
                   f"theorem cert_{k} : emptyCertB {k} cs_{k} = true := by decide +kernel\n\n"
                   f"/-- **`y² = x³ + {k}` has no integral point**, under the class-list premise. -/\n"
                   f"theorem plus{k} (hcls : ClassList {k} (cs_{k}.map Prod.fst)) (x y : ℤ) : y ^ 2 ≠ x ^ 3 + {k} :=\n"
                   f"  no_point_of_cert hcls cert_{k} x y\n")
    out.append('end PerfectPower.Generated.PositiveK\n')
    (ROOT / 'PerfectPower' / 'Generated' / 'PositiveK.lean').write_text('\n'.join(out))


if __name__ == '__main__':
    run()
