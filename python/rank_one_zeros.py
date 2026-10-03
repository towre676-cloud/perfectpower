"""Skolem data for rank-one sources with several solutions (`RankOneZeros.source_list`).

For `g = η` and `g = ε = η⁻¹`, find an odd prime `p` and a period `M = t·M₀` (`p ∤ t`) with
`g^M ≡ 1 (mod p)` such that every class `r < M` passes `RankOneZeros.skolemZB`:
* either `p ∤ (g^r)₂`,
* or `(g^r)₂ = 0` and `p ∤ ((g^{M+r})₂ − (g^r)₂)/p`.
Every zero of the `z²` coordinate is then below `M`, and the solutions are read off and
filtered exactly (`listB`).  This script only searches; the Lean kernel re-checks every condition.

Run: python3 python/rank_one_zeros.py
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

import rank_one_sources as R  # noqa: E402

PRIMES = R.PRIMES


def powz(P, Q, g, n):
    x = (1, 0, 0)
    for _ in range(n):
        x = R.mul(P, Q, x, g)
    return x


def zb(P, Q, g, p, M):
    """Mirror of `RankOneZeros.skolemZB`."""
    if M <= 0:
        return False
    A = R.Mx(P, Q, powz(P, Q, g, M))
    if any((A[i][j] - (i == j)) % p for i in range(3) for j in range(3)):
        return False
    x = (1, 0, 0)
    pows = [x]
    for _ in range(2 * M):
        x = R.mul(P, Q, x, g)
        pows.append(x)
    for r in range(M):
        c = pows[r][2]
        if c % p:
            continue
        if c != 0:
            return False
        d = pows[M + r][2] - c
        if (d // p) % p == 0:
            return False
    return True


def find_zb(P, Q, g, Mmax=400):
    for p in PRIMES:
        x, M0 = g, 1
        while M0 <= Mmax:
            A = R.Mx(P, Q, x)
            if all((A[i][j] - (i == j)) % p == 0 for i in range(3) for j in range(3)):
                break
            x, M0 = R.mul(P, Q, x, g), M0 + 1
        else:
            continue
        for t in range(1, Mmax // M0 + 1):
            if t % p and zb(P, Q, g, p, t * M0):
                return p, t * M0
    return None


def F(P, Q, x):
    u, v = x
    return -u ** 3 + P * u * v ** 2 + Q * v ** 3


def cands(P, Q, eta, eps, M, M1):
    gs = [powz(P, Q, eta, n) for n in range(M)] + [powz(P, Q, eps, n) for n in range(M1)]
    return [y for g in gs for y in ((g[0], -g[1]), (-g[0], g[1]))]


def solve(row):
    P, Q, h = row['P'], row['Q'], row['h']
    eta = tuple(row['eta'])
    eps = R.inverse(P, Q, eta)
    a = find_zb(P, Q, eta)
    b = find_zb(P, Q, eps)
    out = {'k': row['k'], 'form': row['form'], 'P': P, 'Q': Q, 'h': h, 'eta': list(eta), 'eps': list(eps),
           'known_representations': row['known_representations']}
    if not a or not b or a[0] != b[0]:
        # one prime for both directions keeps `[Fact p.Prime]` single; search a common prime
        common = None
        for p in PRIMES:
            fa = find_zb_at(P, Q, eta, p)
            fb = find_zb_at(P, Q, eps, p)
            if fa and fb:
                common = (p, fa, fb)
                break
        if not common:
            out['status'] = 'no_skolem_split'
            return out
        p, M, M1 = common
    else:
        p, M, M1 = a[0], a[1], b[1]
    sols = sorted({x for x in cands(P, Q, eta, eps, M, M1) if F(P, Q, x) == 1})
    out.update({'p': p, 'M': M, 'M_eps': M1, 'solutions_shifted': [list(s) for s in sols],
                'solutions': [[u - h * v, v] for u, v in sols]})
    known = sorted(tuple(r) for r in row['known_representations'])
    out['status'] = 'ok' if sorted((u - h * v, v) for u, v in sols) == known else 'mismatch'
    return out


def find_zb_at(P, Q, g, p, Mmax=400):
    x, M0 = g, 1
    while M0 <= Mmax:
        A = R.Mx(P, Q, x)
        if all((A[i][j] - (i == j)) % p == 0 for i in range(3) for j in range(3)):
            break
        x, M0 = R.mul(P, Q, x, g), M0 + 1
    else:
        return None
    for t in range(1, Mmax // M0 + 1):
        if t % p and zb(P, Q, g, p, t * M0):
            return t * M0
    return None


def main():
    rows = [r for r in json.loads((ROOT / 'receipts' / 'rank_one_blockers.json').read_text())['sources']
            if r['status'] == 'several_solutions']
    res = [solve(r) for r in rows]
    out = {'scope': 'Skolem data for several-solution rank-one sources (RankOneZeros); a search, re-checked by the Lean kernel',
           'summary': {'sources': len(res), 'ok': sum(r['status'] == 'ok' for r in res)}, 'sources': res}
    (ROOT / 'receipts' / 'rank_one_zeros.json').write_text(json.dumps(out, indent=1) + '\n')
    return res


if __name__ == '__main__':
    for r in main():
        print(r['k'], r['form'], r['status'], r.get('p'), r.get('M'), r.get('M_eps'), r.get('solutions'))
