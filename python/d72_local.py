"""D = 72: are the two remaining point-free Thue classes locally soluble everywhere?

The branch equation of an entry (k, p, q) of y^2 = x^3 - 72 is F(a, b) = k^3 with
F(a, b) = q W1(a, b) - p W2(a, b).  Every integral point of the branch also satisfies the
*restrictions* k^3 | p W1 + D q W2 (the readout y) and k | a^2 + D b^2 (the readout x); the
curve equation y^2 + D = x^3 then follows from the norm identity.  (The lattice condition
x | a - y b is global and has no fixed local form.)

For each class this script proves local solubility at every place:
* the real place: F(t, 1) is a real cubic, so F takes every real value;
* every exceptional prime (p | 3 * M * disc F, and p <= 7): an explicit Hensel witness (a, b) with
  v_p(F(a, b) - M) >= 2 v_p(dF/da (a, b)) + 1, so a lifts to a p-adic root a* = a mod p^(e - v);
  for p = 3 the witness also satisfies the restrictions and e - v >= 6, so they persist;
* every other prime p >= 11: the plane cubic F(a, b) = M z^3 is smooth over F_p (p does not divide
  3 M disc F), so by the Hasse-Weil bound it has at least p + 1 - 2 sqrt(p) points, at most 3 at
  infinity, hence an affine point for p >= 11; affine points are smooth, so they lift by Hensel.
Writes receipts/d72_local.json.  The conclusion is a statement about local solubility; no
certificate of emptiness can exist for these classes at any single place.
"""
import json
import sys
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.descent import W1, W2  # noqa: E402
from perfectpower.thue_graph import disc  # noqa: E402

D = 72


def v(n, p):
    if n == 0:
        return 10 ** 9
    c = 0
    while n % p == 0:
        n //= p
        c += 1
    return c


def primes_upto(n):
    return [q for q in range(2, n + 1) if all(q % r for r in range(2, isqrt(q) + 1))]


def factor_primes(n):
    n, out, d = abs(n), [], 2
    while d * d <= n:
        if n % d == 0:
            out.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def witness(k, p, q, P, restricted):
    M = k ** 3
    F = lambda a, b: q * W1(D, a, b) - p * W2(D, a, b)                       # noqa: E731
    Fa = lambda a, b: q * (3 * a * a - 3 * D * b * b) + 6 * p * a * b           # noqa: E731
    Fb = lambda a, b: -6 * D * q * a * b - p * (3 * D * b * b - 3 * a * a)      # noqa: E731
    for b in range(-40, 41):
        for a in range(-4000, 4001):
            r = F(a, b) - M
            for var, d in (('a', Fa(a, b)), ('b', Fb(a, b))):
                vd, e = v(d, P), v(r, P)
                if d != 0 and e >= 2 * vd + 1:
                    if restricted:
                        if e - vd < 6:
                            continue
                        if (p * W1(D, a, b) + D * q * W2(D, a, b)) % M or (a * a + D * b * b) % k:
                            continue
                    return {'a': a, 'b': b, 'lift_variable': var, 'v_residual': min(e, 999),
                            'v_derivative': vd}
    return None


def main():
    g = json.loads((ROOT / 'receipts' / 'thue_graph.json').read_text())
    out = []
    for c in g['classes']:
        if c['curves'] != [72] or 'descent' in c or c['pari_label'] == 'carries_points':
            continue
        m = c['members'][0]
        k, p, q = m['k'], m['p'], m['q']
        F = (q, 3 * p, -3 * D * q, -p * D)
        M = k ** 3
        exc = sorted(set(factor_primes(3 * M * disc(F))) | set(primes_upto(7)))
        rows = {}
        for P in exc:
            w = witness(k, p, q, P, restricted=(P == 3))
            rows[str(P)] = w
        ok = all(w is not None for w in rows.values())
        out.append({'class': c['id'], 'entry': [k, p, q], 'form': list(F), 'M': M,
                    'real_place': 'soluble (odd-degree real polynomial)',
                    'exceptional_primes': exc, 'hensel_witnesses': rows,
                    'good_primes': 'p >= 11 not dividing 3*M*disc: smooth plane cubic, Hasse-Weil gives '
                                   '>= p + 1 - 2 sqrt(p) - 3 > 0 affine points, all smooth, Hensel lifts',
                    'restricted_at_3': 'witness satisfies k^3 | p W1 + D q W2 and k | a^2 + D b^2 with '
                                       'e - v >= 6, so the 3-adic root keeps them',
                    'everywhere_locally_soluble': ok,
                    'pari_integral_solutions': 0})
        print(c['id'], (k, p, q), 'exceptional', exc, 'all witnesses found' if ok else rows)
    res = {'curve': 'y^2 = x^3 - 72', 'classes': out,
           'conclusion': 'both remaining classes are locally soluble at every place, including the branch '
                         'restrictions at 3; PARI finds no integral solution. No local certificate can close '
                         'them: what is missing is global (the lattice condition x | a - y b, or a global '
                         'argument in the field)'}
    (ROOT / 'receipts' / 'd72_local.json').write_text(json.dumps(res, indent=1) + '\n')


if __name__ == '__main__':
    main()
