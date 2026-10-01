"""Finite hypotheses for `UnitPremises.NormRep`: norm representatives by local ramification
(stdlib only, exact).

For `K = Q(x)`, `g = x^3 - P x - Q`, and a norm target `N` with a supplied `γ0` of norm `N`:
1. **Maximal order.**  The index `[O_K : Z[x]]` divides `sqrt(disc g / disc K)`, so only primes with
   `p^2 | disc g` matter.  For each, Dedekind's criterion is checked: write `g ≡ Π ḡ_i^{e_i} (mod p)`
   and `h = (g − Π g_i^{e_i}) / p`; `Z[x]` is `p`-maximal iff no repeated `ḡ_i` divides `h̄`.
2. **Total ramification.**  For every prime `p | N`: `g ≡ (x − r)^3 (mod p)`.  With `p`-maximality,
   Dedekind–Kummer gives `(p) = 𝔭^3`, `N𝔭 = p`, and `𝔭` is the only prime above `p`.
3. Then the only integral ideal of norm `|N| = Π p^{v_p}` is `Π 𝔭_p^{v_p}`, so `(γ) = (γ0)` for every
   `γ` with `|N(γ)| = |N|`, hence `γ = γ0 u` with `u` a unit: `NormRep P Q N [γ0]`.
The script checks 1–2 and `N(γ0) = N` exactly.  Dedekind's criterion and the Dedekind–Kummer
factorization theorem are the cited mathematics (not formalized here).

Run: python3 python/norm_rep_localization.py     Writes receipts/norm_rep_localization.json.
"""
from __future__ import annotations

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def nrm(P, Q, g):
    a, b, c = g
    return (a * ((a + P * c) * (a + P * c) - (P * b + Q * c) * b) - Q * c * (b * (a + P * c) - (P * b + Q * c) * c)
            + Q * b * (b * b - (a + P * c) * c))


def factor_int(n):
    n, out, p = abs(n), {}, 2
    while p * p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def pmul(f, g):
    out = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i + j] += a * b
    return out


def pmod(f, p):
    f = [c % p for c in f]
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return f


def evalp(f, x, p):
    return sum(c * pow(x, i, p) for i, c in enumerate(f)) % p


def linear_factorization(g, p):
    """g mod p as Π (x - r)^e, if it splits into linear factors (coefficients low to high)."""
    roots, f = [], pmod(g, p)
    for r in range(p):
        while len(f) > 1 and evalp(f, r, p) == 0:
            # synthetic division by (x - r)
            q, acc = [0] * (len(f) - 1), 0
            for i in range(len(f) - 1, 0, -1):
                acc = (acc * r + f[i]) % p
                q[i - 1] = acc
            f = pmod(q, p)
            roots.append(r)
    if len(f) != 1:
        return None
    return {r: roots.count(r) for r in sorted(set(roots))}


def dedekind(g, p):
    fac = linear_factorization(g, p)
    if fac is None:
        raise SystemExit(f'g does not split into linear factors mod {p}: extend the check')
    prod = [1]
    for r, e in fac.items():
        for _ in range(e):
            prod = pmul(prod, [-r, 1])
    diff = [a - b for a, b in zip(g, prod)]
    assert all(c % p == 0 for c in diff)
    h = [c // p for c in diff]
    ok = all(evalp(h, r, p) != 0 for r, e in fac.items() if e >= 2)
    return {'p': p, 'factorization_mod_p': {str(r): e for r, e in fac.items()}, 'h': h,
            'p_maximal': ok, 'totally_ramified': len(fac) == 1 and list(fac.values()) == [3]}


def field(P, Q, targets):
    g = [-Q, -P, 0, 1]
    disc = 4 * P ** 3 - 27 * Q ** 2
    primes = sorted(p for p, e in factor_int(disc).items() if e >= 2)
    local = {p: dedekind(g, p) for p in primes}
    rows = []
    for N, g0 in targets:
        assert nrm(P, Q, g0) == N, (N, g0)
        support = sorted(factor_int(N))
        for p in support:
            if p not in local:
                local[p] = dedekind(g, p)
        ok = all(local[p]['totally_ramified'] and local[p]['p_maximal'] for p in support)
        rows.append({'N': N, 'gamma0': list(g0), 'support': support, 'unique_ideal_of_norm_N': ok})
        assert ok, f'N = {N}: some prime of the support is not totally ramified and p-maximal'
    assert all(v['p_maximal'] for v in local.values()), 'Z[x] is not maximal'
    return {'P': P, 'Q': Q, 'poly_disc': disc, 'index_primes': primes,
            'local': [local[p] for p in sorted(local)], 'O_K_equals_Z_x': True, 'targets': rows}


def main():
    f756 = json.loads((ROOT / 'receipts' / 'field756_bound.json').read_text())
    d72 = json.loads((ROOT / 'receipts' / 'd72_thue_bound.json').read_text())
    t756 = sorted({(c['form'][0] ** 2 * c['M'], tuple(c['gammas'][0])) for c in f756['classes']})
    for c in f756['classes']:
        assert len(c['gammas']) == 1
    al = tuple(d72['gammas'][0])
    out = {'label': 'exact finite hypotheses of Dedekind\'s criterion and Dedekind–Kummer; the theorems '
                    'themselves are cited, not formalized',
           'fields': [field(6, 2, t756), field(9, 6, [(9, al)] + [(-9, tuple(-x for x in al))])]}
    (ROOT / 'receipts' / 'norm_rep_localization.json').write_text(json.dumps(out, indent=1) + '\n')
    for f in out['fields']:
        print(f"x^3 - {f['P']}x - {f['Q']}: disc {f['poly_disc']}, index primes {f['index_primes']}, "
              + ', '.join(f"p={l['p']}: {l['factorization_mod_p']} max={l['p_maximal']} tot={l['totally_ramified']}"
                          for l in f['local'])
              + f"; targets {[t['N'] for t in f['targets']]} all unique")


if __name__ == '__main__':
    main()
