"""Rank-one sources with several solutions (`RankOneZeros.source_list`, `SkolemZeros.corner_zeros2`).

For `g = η` and `g = ε = η⁻¹`, find an odd prime `p`, the period `M` of `g` modulo `p`, and
auxiliary primes `[(q, M_q)]`, such that every class `r < M` passes one test of
`RankOneZeros.skolemZB2`:
* `p ∤ (g^r)₂` (no zero);
* `(g^r)₂ = 0` and `p ∤ ((g^{M+r})₂ − (g^r)₂)/p` (the single zero `r`);
* `0 < r`, `(h^{M−r})₂ = 0` and `p ∤ ((g^r)₂ − (h^{M−r})₂)/p`, `h = g⁻¹` (recentred at the root
  `−(M−r)` of the other direction: no zero `N ≥ 0`);
* an auxiliary prime with `g^{M_q} ≡ 1 (mod q)` and `q ∤ (g^s)₂` for all `s < M_q`,
  `s ≡ r (mod gcd(M, M_q))` (no zero).
Every zero is then below `M`; the solutions are the candidates that satisfy the equation
(`listB`).  This script only searches and writes the Lean modules; the kernel re-checks all of it.

Run: python3 python/rank_one_zeros.py
"""
from __future__ import annotations

import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

import rank_one_sources as R  # noqa: E402

# (k, standard form F = (−1, B, C, d), P, Q, shift h, η, known representations): the irreducible
# positive-k sources with several known solutions (found by `python/rank_one_scan.py`).
TARGETS = [
    (1, (-1, 0, 0, -2), 0, -2, 0, (1, -1, 1), [(-1, 0), (1, -1)]),
    (8, (-1, -3, 3, -3), 6, -8, 1, (3, -3, 1), [(-4, 1), (-1, 0)]),
    (9, (-1, 0, -6, -2), -6, -2, 0, (55, -3, 9), [(-1, 0), (-1, 3)]),
    (15, (-1, -3, 0, -6), 3, -8, 1, (13, -10, 4), [(-7, 2), (-1, 0)]),
    (17, (-1, -3, 3, -5), 6, -10, 1, (3, -3, 1), [(-1, 0), (4, -1)]),
    (17, (-1, 0, -6, -6), -6, -6, 0, (7, -1, 1), [(-1, 0), (-1, 1), (23, -26)]),
    (17, (-1, 0, -3, -8), -3, -8, 0, (21, -6, 4), [(-1, 0), (3, -2)]),
    (24, (-1, 0, -6, -8), -6, -8, 0, (7, -1, 1), [(-1, 0), (1, -1), (31, -28)]),
    (65, (-1, 0, -12, -2), -12, -2, 0, (433, -6, 36), [(-1, 0), (-1, 6)]),
    (68, (-1, 0, -12, -4), -12, -4, 0, (109, -3, 9), [(-1, 0), (-1, 3)]),
    (73, (-1, -6, 6, -6), 18, -34, 2, (7, -5, 1), [(-7, 1), (-1, 0)]),
    (73, (-1, 0, -12, -6), -12, -6, 0, (49, -2, 4), [(-1, 0), (-1, 2)]),
    (100, (-1, 0, -12, -12), -12, -12, 0, (13, -1, 1), [(-1, 0), (-1, 1)]),
    (100, (-1, 0, 0, -20), 0, -20, 0, (361, -133, 49), [(-1, 0), (19, -7)]),
]


def pows(P, Q, g, n):
    pw = [(1, 0, 0)]
    for _ in range(n):
        pw.append(R.mul(P, Q, pw[-1], g))
    return pw


def order(P, Q, g, p, Mmax=800):
    x = g
    for M in range(1, Mmax + 1):
        A = R.Mx(P, Q, x)
        if all((A[i][j] - (i == j)) % p == 0 for i in range(3) for j in range(3)):
            return M
        x = R.mul(P, Q, x, g)
    return None


def bad_classes(P, Q, g, h, p, M):
    pw, ph = pows(P, Q, g, 2 * M), pows(P, Q, h, M)
    bad = []
    for r in range(M):
        c = pw[r][2]
        if c % p == 0 and not (c == 0 and ((pw[M + r][2] - c) // p) % p) \
                and not (r > 0 and ph[M - r][2] == 0 and ((c - ph[M - r][2]) // p) % p):
            bad.append(r)
    return bad


def aux_cover(P, Q, g, M, bad, p):
    left, used = set(bad), []
    for q in R.PRIMES:
        if q == p or not left:
            continue
        Mq = order(P, Q, g, q)
        if not Mq:
            continue
        G = math.gcd(M, Mq)
        pw = pows(P, Q, g, Mq)
        cov = {r for r in left if all(pw[s][2] % q for s in range(Mq) if s % G == r % G)}
        if cov:
            used.append((q, Mq))
            left -= cov
    return used if not left else None


def zb2(P, Q, g, h, p, M, aux, K):
    """Mirror of `RankOneZeros.skolemZB2`."""
    G, H = pows(P, Q, g, K), pows(P, Q, h, M)
    one = lambda x, q: all((R.Mx(P, Q, x)[i][j] - (i == j)) % q == 0 for i in range(3) for j in range(3))
    if not (0 < M and 2 * M <= K and one(G[M], p)):
        return False
    if not all(0 < Mq <= K and one(G[Mq], q) for q, Mq in aux):
        return False
    c = [x[2] for x in G]
    for r in range(M):
        ok = (c[r] % p != 0
              or (c[r] == 0 and ((c[M + r] - c[r]) // p) % p != 0)
              or (r > 0 and H[M - r][2] == 0 and ((c[r] - H[M - r][2]) // p) % p != 0)
              or any(all(s >= Mq or s % math.gcd(M, Mq) != r % math.gcd(M, Mq) or c[s] % q != 0
                         for s in range(K + 1)) for q, Mq in aux))
        if not ok:
            return False
    return True


def F(P, Q, x):
    u, v = x
    return -u ** 3 + P * u * v ** 2 + Q * v ** 3


def cands(P, Q, eta, eps, M, M1):
    gs = pows(P, Q, eta, M - 1) + pows(P, Q, eps, M1 - 1)
    return [y for g in gs for y in ((g[0], -g[1]), (-g[0], g[1]))]


def search(P, Q, eta, eps):
    for p in R.PRIMES:
        out = []
        for g, h in ((eta, eps), (eps, eta)):
            M = order(P, Q, g, p, 500)
            if not M:
                break
            bad = bad_classes(P, Q, g, h, p, M)
            aux = aux_cover(P, Q, g, M, bad, p) if bad else []
            if aux is None:
                break
            K = max([2 * M] + [Mq for _, Mq in aux])
            assert zb2(P, Q, g, h, p, M, aux, K)
            out.append({'M': M, 'aux': aux, 'K': K, 'bad_classes': len(bad)})
        if len(out) == 2:
            return p, out
    return None


def find(k, Fm, P, Q, h, start):
    eta, c = R.fundamental(P, Q, start)
    eps = R.inverse(P, Q, eta)
    a, B, C, d = Fm
    assert (a, B, C, d) == (-1, -3 * h, -3 * h * h + P, -h ** 3 + P * h + Q), (k, Fm)
    return {'k': k, 'form': list(Fm), 'P': P, 'Q': Q, 'h': h, 'eta': list(eta), 'eps': list(eps),
            'cert': {x: str(v) for x, v in c.items() if not x.startswith('_')},
            'slab_elements': sum(1 for _ in R.slab(P, c)), '_c': c,
            'skolem_eta': {'p': 3, 'M': 1}, 'skolem_eps': {'p': 3, 'M': 1}}


def _l(L):
    return '[' + ', '.join(f'({R._i(u)}, {R._i(v)})' for u, v in L) + ']'


def _aux(a):
    return '[' + ', '.join(f'({q}, {Mq})' for q, Mq in a) + ']'


HEAD = """import PerfectPower.RankOneZeros

/-!
# Rank-one sources with several solutions for `k = {k}` (generated by `python/rank_one_zeros.py`)

Each source `F(u, v) = −N((u + hv) − vz)` in `ℤ[z]`, `z³ = Pz + Q`, gets
`−u³ + P u v² + Q v³ = 1 ↔ (u, v) ∈ L` from `RankOneZeros.source_list`:
* **Units.** Unit generation is as in `RankOne` (the certificate `condB` and the slab check).
* **Zero set.** The zeros of the `z²` coordinate of `ηⁿ` lie below an explicit bound in each
  direction (`SkolemZeros.corner_zeros2`: a Skolem prime, recentring at known roots, auxiliary
  primes), and one kernel check filters the candidates.
-/

set_option Elab.async false

namespace PerfectPower.Generated.RankOneZeros.K{k}

open PerfectPower UnitBox UnitPremises RankOne RankOneZeros

"""


def lean_block(r, i):
    base = R.lean_block(r, i)
    base = base[:base.index(f"theorem skη_{i}")]
    P, Q = r['P'], r['Q']
    PQ = f'{R._i(P)} {R._i(Q)}'
    zd = r['zeros']
    p, (de, dx) = zd['p'], zd['dirs']
    L = r['solutions_shifted']
    return base + (
        f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
        f"theorem zη_{i} : skolemZB2 {PQ} η{i} ε{i} {p} {de['M']} {_aux(de['aux'])} {de['K']} = true := by decide +kernel\n\n"
        f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
        f"theorem zε_{i} : skolemZB2 {PQ} ε{i} η{i} {p} {dx['M']} {_aux(dx['aux'])} {dx['K']} = true := by decide +kernel\n\n"
        f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats 0 in\n"
        f"theorem list_{i} : listB {PQ} η{i} ε{i} {de['M']} {dx['M']} {_l(L)} = true := by decide +kernel\n\n"
        f"/-- **Source {i}**: `−u³ + ({P}) u v² + ({Q}) v³ = 1 ↔ (u, v) ∈ {_l(L)}`. -/\n"
        f"theorem source{i} (u v : ℤ) : -u ^ 3 + {R._i(P)} * u * v ^ 2 + {R._i(Q)} * v ^ 3 = 1 ↔ (u, v) ∈ ({_l(L)} : List (ℤ × ℤ)) :=\n"
        f"  haveI : Fact (Nat.Prime {p}) := ⟨by norm_num⟩\n"
        f"  source_list h1_{i} h2_{i} n1_{i} n2_{i} cond_{i} slab_{i} (zeros2_of h1_{i} (by norm_num) zη_{i})\n"
        f"    (zeros2_of h2_{i} (by norm_num) zε_{i}) list_{i} u v\n")


def main(write=True):
    rows = [{'k': k, 'form': list(F), 'P': P, 'Q': Q, 'h': h, 'eta': list(eta),
             'known_representations': [list(x) for x in reps]} for k, F, P, Q, h, eta, reps in TARGETS]
    res, by_k = [], {}
    for row in rows:
        P, Q, h = row['P'], row['Q'], row['h']
        r = find(row['k'], tuple(row['form']), P, Q, h, tuple(row['eta']))
        eta, eps = tuple(r['eta']), tuple(r['eps'])
        s = search(P, Q, eta, eps)
        out = {k: v for k, v in r.items() if not k.startswith('_') and not k.startswith('skolem')}
        out['known_representations'] = row['known_representations']
        if not s:
            out['status'] = 'no_zero_certificate'
            res.append(out)
            continue
        p, dirs = s
        L = sorted({x for x in cands(P, Q, eta, eps, dirs[0]['M'], dirs[1]['M']) if F(P, Q, x) == 1})
        out.update({'zeros': {'p': p, 'dirs': dirs}, 'solutions_shifted': [list(x) for x in L],
                    'solutions': [[u - h * v, v] for u, v in L]})
        known = sorted(tuple(x) for x in row['known_representations'])
        out['status'] = 'ok' if sorted((u - h * v, v) for u, v in L) == known else 'new_solutions'
        res.append(out)
        r.update(out)
        by_k.setdefault(row['k'], []).append(r)
    if write:
        d = ROOT / 'PerfectPower' / 'Generated' / 'RankOneZeros'
        d.mkdir(exist_ok=True)
        for k, rs in by_k.items():
            text = HEAD.replace('{k}', str(k)) + '\n'.join(lean_block(r, i) for i, r in enumerate(rs)) + \
                f'\nend PerfectPower.Generated.RankOneZeros.K{k}\n'
            (d / f'K{k}.lean').write_text(text)
        (ROOT / 'receipts' / 'rank_one_zeros.json').write_text(json.dumps(
            {'scope': 'several-solution rank-one sources (RankOneZeros.source_list); every condition is '
                      're-checked by the Lean kernel',
             'summary': {'sources': len(res), 'ok': sum(r['status'] == 'ok' for r in res)},
             'sources': res}, indent=1) + '\n')
    return res


if __name__ == '__main__':
    for r in main():
        z = r.get('zeros')
        print(r['k'], r['form'], r['status'], z and z['p'], z and [(d['M'], d['aux'], d['K']) for d in z['dirs']],
              r.get('solutions'))
