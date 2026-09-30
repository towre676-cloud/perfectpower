"""A finite, exhaustive branch compiler for y^2 = x^3 - D (D > 0), checked by Lean
(`PerfectPower/DescentBranch.lean`).

Every integral point enters a branch
------------------------------------
`ClassTwo.short_relation` (Thue's lattice lemma on I = {(a, b) : x | a - y b}) gives, for every
solution, integers a, b and a table entry (k, p, q) with

    1 <= k <= K,   p^2 + D q^2 = k^3,   k^3 (y + s) = (p + q s) (a + b s)^3,    s = sqrt(-D).

No coprimality of y + s and y - s is assumed: common factors (primes over 2 and over D, and the
conductor of Z[s]) show up as table entries, which must be discharged like every other entry.
The table is finite (k <= K from the Thue box, |q| <= Q), so the branches are finite.

Each branch is closed in one of two ways
----------------------------------------
* **Field cube.**  g^3 (p + q s) = (c + d s)^3 for integers c, d, g >= 1: the entry is a cube in
  Q(s) (a unit such as i = (-i)^3, an element cube such as 2 + 2i = (i - 1)^3, or a half-integral
  cube (c + d s)/2 of the maximal order).  With A + B s = (c + d s)(a + b s) the branch becomes

      g^3 k^3 (y + s) = (A + B s)^3,  so  B (3 A^2 - D B^2) = g^3 k^3,

  a *reducible* cubic: B divides g^3 k^3, A is then determined up to sign, and every y of the
  branch is in an explicit finite list.  No class number, maximal order or residue check is used.
* **Local obstruction.**  The branch equation's s-coordinate, q W1(a, b) - p W2(a, b) = k^3 (a
  binary cubic in a, b), has no solution modulo m.

An entry that is neither is an irreducible Thue equation; the curve is then *not* closed here
(`OPEN_BRANCH`), however plausible its point list.

Every accepted candidate returns to the curve: the final list is filtered by y^2 + D = x^3
exactly (both directions are Lean theorems).
"""
from __future__ import annotations

from math import isqrt

from .descent import W1, W2, thue_box


def icbrt(n: int) -> int:
    """Floor cube root (any sign)."""
    if n < 0:
        r = icbrt(-n)
        return -r if r ** 3 == -n else -r - 1
    if n < 2:
        return n
    r = 1 << -(-n.bit_length() // 3)   # exact integer Newton from above (no floats)
    while True:
        s = (2 * r + n // (r * r)) // 3
        if s >= r:
            break
        r = s
    while r ** 3 > n:
        r -= 1
    while (r + 1) ** 3 <= n:
        r += 1
    return r


def table(D: int, K: int, Q: int) -> list[tuple[int, int, int]]:
    """All (k, p, q) with 1 <= k <= K, |q| <= Q, p^2 + D q^2 = k^3."""
    out = []
    for k in range(1, K + 1):
        for q in range(-Q, Q + 1):
            t = k ** 3 - D * q * q
            if t < 0:
                continue
            p = isqrt(t)
            if p * p == t:
                out.extend([(k, p, q)] if p == 0 else [(k, p, q), (k, -p, q)])
    return out


def cube_witness(D: int, k: int, p: int, q: int, gmax: int = 6):
    """(c, d, g) with g^3 (p + q s) = (c + d s)^3, or None."""
    for g in range(1, gmax + 1):
        n = k * g * g
        for d in range(-isqrt(n // D) - 1, isqrt(n // D) + 2):
            t = n - D * d * d
            if t < 0:
                continue
            c0 = isqrt(t)
            if c0 * c0 != t:
                continue
            for c in {c0, -c0}:
                if (c ** 3 - 3 * D * c * d * d, 3 * c * c * d - D * d ** 3) == (g ** 3 * p, g ** 3 * q):
                    return c, d, g
    return None


def branch_form(D: int, p: int, q: int):
    """The s-coordinate q W1(a, b) - p W2(a, b) of (p + q s)(a + b s)^3, as a function."""
    return lambda a, b: q * W1(D, a, b) - p * W2(D, a, b)


MODULI = [m for m in range(2, 64)] + [64, 72, 81, 96, 100, 108, 121, 125, 128, 144, 169]


def local_obstruction(D: int, k: int, p: int, q: int, moduli=MODULI):
    """A modulus m with q W1 - p W2 != k^3 (mod m) for all a, b; or None."""
    F = branch_form(D, p, q)
    for m in moduli:
        target = k ** 3 % m
        if all((F(a, b) - target) % m for a in range(m) for b in range(m)):
            return m
    return None


def branch_ys(D: int, k: int, g: int) -> list[int]:
    """All y with g^3 k^3 y = A^3 - 3 D A B^2 for some A, B with B (3 A^2 - D B^2) = g^3 k^3."""
    M = g ** 3 * k ** 3
    ys = set()
    for B in range(-M, M + 1):
        if B == 0 or M % B:
            continue
        t = M // B + D * B * B
        if t % 3:
            continue
        a0 = isqrt(t // 3) if t >= 0 else -1
        if a0 < 0 or a0 * a0 * 3 != t:
            continue
        for A in {a0, -a0}:
            num = A ** 3 - 3 * D * A * B * B
            if num % M == 0:
                ys.add(num // M)
    return sorted(ys)


def compile_curve(D: int, max_K: int = 60) -> dict:
    """The branch certificate for y^2 = x^3 - D, or the open branches."""
    K, r, t = thue_box(D)
    rec = {'D': D, 'k': -D, 'K': K, 'r': r, 't': t}
    if K > max_K:
        return {**rec, 'status': 'BOX_TOO_LARGE'}
    Q = 0
    while D * (Q + 1) ** 2 <= K ** 3:
        Q += 1
    rec['Q'] = Q
    entries, open_, ys = [], [], set()
    for (k, p, q) in table(D, K, Q):
        w = cube_witness(D, k, p, q)
        if w is not None:
            c, d, g = w
            by = branch_ys(D, k, g)
            ys.update(by)
            entries.append({'k': k, 'p': p, 'q': q, 'cube': [c, d, g], 'ys': by})
            continue
        m = local_obstruction(D, k, p, q)
        if m is not None:
            entries.append({'k': k, 'p': p, 'q': q, 'mod': m})
            continue
        open_.append({'k': k, 'p': p, 'q': q})
    rec['entries'] = entries
    pts = []
    for y in sorted(ys):
        x = icbrt(y * y + D)
        if x ** 3 == y * y + D:
            pts.append((x, y))
    rec['candidate_ys'] = sorted(ys)
    rec['points'] = sorted(set(pts))
    if open_:
        rec['status'] = 'OPEN_BRANCH'
        rec['open'] = open_
    else:
        rec['status'] = 'COMPLETE'
    return rec


def _i(v):
    return f'({v})' if v < 0 else str(v)


def lean_args(c: dict) -> dict:
    """The data a Lean certificate needs: cube and modulus verdicts, candidates, points."""
    cubes = [(e['k'], e['p'], e['q'], *e['cube']) for e in c['entries'] if 'cube' in e]
    mods = [(e['k'], e['p'], e['q'], e['mod']) for e in c['entries'] if 'mod' in e]
    return {'cubes': cubes, 'mods': mods, 'Ys': c['candidate_ys'], 'P': c['points']}


def lean_theorem(name: str, c: dict) -> str:
    """`theorem name : ∀ x y, y^2 = x^3 - D ↔ (x, y) ∈ P` from a COMPLETE branch certificate."""
    assert c['status'] == 'COMPLETE'
    a = lean_args(c)
    D = c['D']
    cubes = '[' + ', '.join('(' + ', '.join(_i(v) for v in t) + ')' for t in a['cubes']) + ']'
    mods = '[' + ', '.join('(' + ', '.join(_i(v) for v in t) + ')' for t in a['mods']) + ']'
    ys = '[' + ', '.join(_i(v) for v in a['Ys']) + ']'
    pts = '[' + ', '.join(f'({_i(x)}, {_i(y)})' for x, y in a['P']) + ']'
    return (f"set_option maxHeartbeats 0 in\n/-- **The complete list of integral points of `y^2 = x^3 - {D}`**: {len(a['P'])} point(s). "
            f"Branches: {len(a['cubes'])} field-cube entries, {len(a['mods'])} locally impossible. -/\n"
            f"theorem {name} (x y : ℤ) : y ^ 2 = x ^ 3 - {D} ↔ (x, y) ∈ ({pts} : List (ℤ × ℤ)) :=\n"
            f"  DescentBranch.complete_of_branch {D} (by norm_num) {c['r']} {c['t']} (by norm_num) (by norm_num)"
            f" {c['K']} {c['Q']}\n    (by norm_num) (by norm_num)\n"
            f"    {cubes}\n    {mods}\n    {ys}\n    {pts}\n"
            f"    (by decide +kernel) (by decide +kernel) x y\n")
