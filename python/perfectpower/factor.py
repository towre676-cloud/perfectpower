"""Factorization of integer polynomials over Q (Berlekamp–Zassenhaus, standard library only).

factor_squarefree(f) returns the irreducible factors over Z of a squarefree primitive f with
positive leading coefficient: factor f modulo a prime p that keeps it squarefree
(Cantor–Zassenhaus: distinct-degree, then equal-degree splitting), lift the factorization
p-adically past twice the Mignotte bound (linear Hensel lifting, one factor at a time), and
recombine subsets of the lifted factors, keeping those that divide over Z.

Each returned factor is verified by exact division, and their product is f, so a wrong factor
is impossible.  An exponential recombination can in principle be slow; when the number of
modular factors exceeds `max_modular`, the remainder is returned unfactored and flagged.
Coefficient lists run from the constant term up.
"""
from __future__ import annotations

import random
from itertools import combinations
from math import gcd, isqrt


def _trim(f):
    f = list(f)
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return f


def _deg(f):
    return len(_trim(f)) - 1 if any(f) else -1


# ---------------------------------------------------------------------------
# arithmetic modulo m (m prime or prime power); polynomials are lists, low to high
# ---------------------------------------------------------------------------

def _mod(f, m):
    return _trim([c % m for c in f]) if f else [0]


def _sub(f, g, m):
    n = max(len(f), len(g))
    return _mod([(f[i] if i < len(f) else 0) - (g[i] if i < len(g) else 0) for i in range(n)], m)


def _mul(f, g, m):
    if not any(f) or not any(g):
        return [0]
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                out[i + j] += a * b
    return _mod(out, m)


def _divmod_monic(f, g, m):
    """f = q g + r modulo m, g monic modulo m."""
    f = _mod(f, m)
    dg = _deg(g)
    if _deg(f) < dg:
        return [0], f
    q = [0] * (len(f) - dg)
    r = list(f)
    for i in range(len(f) - 1, dg - 1, -1):
        c = r[i] % m
        if c:
            q[i - dg] = c
            for j in range(dg + 1):
                r[i - dg + j] = (r[i - dg + j] - c * g[j]) % m
    return _mod(q, m), _mod(r[:dg] or [0], m)


def _monic(f, p):
    f = _mod(f, p)
    inv = pow(f[-1], -1, p)
    return _mod([c * inv for c in f], p)


def _gcd(f, g, p):
    f, g = _mod(f, p), _mod(g, p)
    while any(g):
        g = _monic(g, p)
        f, g = g, _divmod_monic(f, g, p)[1]
    return _monic(f, p) if any(f) else [0]


def _powmod(base, e, mod, p):
    result, base = [1], _divmod_monic(base, mod, p)[1]
    while e:
        if e & 1:
            result = _divmod_monic(_mul(result, base, p), mod, p)[1]
        base = _divmod_monic(_mul(base, base, p), mod, p)[1]
        e >>= 1
    return result


def _xgcd(f, g, p):
    """s, t with s f + t g = 1 modulo p (f, g coprime)."""
    r0, r1 = _mod(f, p), _mod(g, p)
    s0, s1, t0, t1 = [1], [0], [0], [1]
    while any(r1):
        inv = pow(r1[_deg(r1)], -1, p)
        q, r = _divmod_monic(r0, _mod([c * inv for c in r1], p), p)
        q = _mod([c * inv for c in q], p)
        r0, r1 = r1, r
        s0, s1 = s1, _sub(s0, _mul(q, s1, p), p)
        t0, t1 = t1, _sub(t0, _mul(q, t1, p), p)
    inv = pow(r0[0], -1, p)
    return _mod([c * inv for c in s0], p), _mod([c * inv for c in t0], p)


def _derivative(f):
    return [i * f[i] for i in range(1, len(f))] or [0]


# ---------------------------------------------------------------------------
# factorization modulo p
# ---------------------------------------------------------------------------

def _factor_mod_p(f, p, rng):
    """Monic irreducible factors of a monic squarefree f modulo an odd prime p."""
    out = []
    # distinct-degree factorization
    h = [0, 1]
    rest = list(f)
    d = 0
    while _deg(rest) >= 2 * (d + 1):
        d += 1
        h = _powmod(h, p, rest, p)
        g = _gcd(rest, _sub(h, [0, 1], p), p)
        if _deg(g) > 0:
            out.extend(_equal_degree(g, d, p, rng))
            rest = _divmod_monic(rest, g, p)[0]
            h = _divmod_monic(h, rest, p)[1] if _deg(rest) > 0 else h
    if _deg(rest) > 0:
        out.append(_monic(rest, p))
    return out


def _equal_degree(f, d, p, rng):
    if _deg(f) == d:
        return [_monic(f, p)]
    while True:
        a = [rng.randrange(p) for _ in range(_deg(f))]
        if _deg(_mod(a, p)) < 1:
            continue
        b = _sub(_powmod(a, (p ** d - 1) // 2, f, p), [1], p)
        g = _gcd(f, b, p)
        if 0 < _deg(g) < _deg(f):
            return (_equal_degree(g, d, p, rng) +
                    _equal_degree(_divmod_monic(f, g, p)[0], d, p, rng))


# ---------------------------------------------------------------------------
# Hensel lifting and recombination
# ---------------------------------------------------------------------------

def _lift(f, g, h, p, k):
    """f = lc * g * h (mod p), g monic: lift g to g' monic with g' | f modulo p^k."""
    s, t = _xgcd(g, h, p)          # s g + t h = 1 (mod p)
    pk = p
    lc = f[-1]
    for _ in range(k - 1):
        m = pk * p
        # h from f and g modulo pk: f = g * h (mod pk)
        e = _sub(f, _mul(g, h, m), m)
        e = [c // pk for c in e]    # exact: f - g h = 0 (mod pk)
        e = _mod(e, p)
        r = _divmod_monic(_mul(t, e, p), g, p)[1]
        g = _mod([gi + pk * ri for gi, ri in zip(g + [0] * len(r), r + [0] * len(g))][:len(g)], m)
        g[-1] = 1
        h = _divmod_monic(_mod(f, m), g, m)[0]
        pk = m
    return g, h


def _symmetric(f, m):
    return _trim([c - m if c > m // 2 else c for c in (x % m for x in f)])


def _divides(f, g):
    """(True, quotient) if g divides f over Z."""
    f, g = list(f), list(g)
    dg = _deg(g)
    if dg < 0 or _deg(f) < dg:
        return False, None
    q = [0] * (len(f) - dg)
    for i in range(len(f) - 1, dg - 1, -1):
        c, rem = divmod(f[i], g[-1])
        if rem:
            return False, None
        q[i - dg] = c
        for j in range(dg + 1):
            f[i - dg + j] -= c * g[j]
    if any(f[:dg]):
        return False, None
    return True, _trim(q)


def _primitive(f):
    c = 0
    for x in f:
        c = gcd(c, x)
    f = [x // c for x in f]
    return f if f[-1] > 0 else [-x for x in f]


def factor_squarefree(f, max_modular: int = 16, seed: int = 0):
    """(factors, remainder): irreducible factors over Z of a squarefree primitive integer
    polynomial f (positive leading coefficient), and the unfactored remainder ([] when fully
    factored)."""
    f = _primitive(_trim([int(c) for c in f]))
    n = _deg(f)
    if n <= 1:
        return [f], []
    rng = random.Random(seed)
    lc = f[-1]
    # a prime keeping f squarefree and of full degree
    p = 3
    while True:
        if lc % p and _deg(_gcd(_monic(f, p), _derivative(_monic(f, p)), p)) == 0:
            break
        p += 2
        while any(p % q == 0 for q in range(3, isqrt(p) + 1, 2)):
            p += 2
    mods = _factor_mod_p(_monic(f, p), p, rng)
    if len(mods) == 1:
        return [f], []
    if len(mods) > max_modular:
        return [], f
    # lift past twice the Mignotte bound for lc * factor
    norm = isqrt(sum(c * c for c in f)) + 1
    bound = 2 * abs(lc) * (2 ** n) * norm + 1
    k = 1
    while p ** k <= bound:
        k += 1
    m = p ** k
    lifted = []
    cur = _mod(f, m)
    for i, g in enumerate(mods[:-1]):
        h = _mod([lc * c for c in _prod(mods[i + 1:], p)], p)
        g_l, cur = _lift(cur, g, h, p, k)
        lifted.append(g_l)
    lifted.append(_monic_mod(cur, m))
    # recombination
    factors = []
    rest = f
    remaining = list(range(len(lifted)))
    size = 1
    while 2 * size <= len(remaining):
        found = False
        for S in combinations(remaining, size):
            cand = [rest[-1]]
            for i in S:
                cand = _mul(cand, lifted[i], m)
            cand = _primitive(_symmetric(cand, m))
            ok, q = _divides(rest, cand)
            if ok:
                factors.append(cand)
                rest = _primitive(q)
                remaining = [i for i in remaining if i not in S]
                found = True
                break
        if not found:
            size += 1
    factors.append(rest)
    return sorted(factors, key=lambda g: (len(g), g)), []


def _prod(polys, p):
    out = [1]
    for g in polys:
        out = _mul(out, g, p)
    return out


def _monic_mod(f, m):
    f = _mod(f, m)
    inv = pow(f[-1], -1, m)
    return _mod([c * inv for c in f], m)
