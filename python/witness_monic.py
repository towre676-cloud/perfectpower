"""Witness-based monic normalization of the nonmonic positive-k Thue sources (`receipts/witness_monic.json`).

For a binary cubic `F` with a recorded point `F(p, q) = 1`, `gcd(p, q) = 1` (a common divisor `g`
gives `g³ ∣ 1`).  Bézout `p s − q r = 1` completes `(−p, −q)` to the first column of
`U = (−p r; −q s)` with `det U = 1` up to sign, and `G(u, v) = F(U(u, v))` has `G(1, 0) = F(−p, −q) = −1`:
the engine's sign convention.  The forms here are classes of `y² = x³ + k`, so their middle
coefficients stay divisible by 3 under `GL₂(ℤ)`; `G` therefore has the shifted shape
`−N((u + hv) − vz)` in `ℤ[z]`, `z³ = Pz + Q` (`positive_k_next.monic_order`).  The second column
`(r, s)` is free up to `(r, s) + t(p, q)`, which moves `h` by `t`; it is chosen so `|h| ≤ 1`.

Completeness transports exactly (`LatticeTransport.complete_of_unimodular`): `F = 1` has the list
`U · L` when `G = 1` has the list `L`.  This script removes the representation obstacle only;
unit generation, Skolem data and the slab size are then classified exactly as in
`python/rank_one_scan.py`, and only a Lean source theorem would be a proof.

Run: python3 python/witness_monic.py [cmax]
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

import positive_k_next as PK  # noqa: E402
import rank_one_scan as S  # noqa: E402


def cubic(F, u, v):
    a, b, c, d = F
    return a * u ** 3 + b * u ** 2 * v + c * u * v ** 2 + d * v ** 3


def egcd(a, b):
    if b == 0:
        return (a, 1, 0) if a >= 0 else (-a, -1, 0)
    g, x, y = egcd(b, a % b)
    return g, y, x - (a // b) * y


def compose(F, U):
    """Coefficients of `G(u, v) = F(U(u, v))`, `U = (α β; γ δ)` acting on columns."""
    (al, be), (ga, de) = U
    # interpolate the cubic G at four points (exact; G is a binary cubic)
    G1 = cubic(F, al, ga)                      # G(1,0)
    G4 = cubic(F, be, de)                      # G(0,1)
    s1 = cubic(F, al + be, ga + de)            # G(1,1) = a+b+c+d
    s2 = cubic(F, al - be, ga - de)            # G(1,-1) = a-b+c-d
    b_plus_c = s1 - G1 - G4
    b_minus_c = -(s2 - G1 + G4)
    b, c = (b_plus_c + b_minus_c) // 2, (b_plus_c - b_minus_c) // 2
    G = (G1, b, c, G4)
    for u, v in ((2, 1), (1, 2), (3, -1), (-2, 5)):
        assert cubic(G, u, v) == cubic(F, al * u + be * v, ga * u + de * v)
    return G


def normalize(F, rep):
    p, q = rep
    assert cubic(F, p, q) == 1
    g, x, y = egcd(p, q)
    assert g == 1                               # forced by F(p, q) = 1
    # (−p)·s − r·(−q) = 1 with s = −x, r = y:  −p(−x) + q y = px + qy = 1
    r, s = y, -x
    U = ((-p, r), (-q, s))
    assert -p * s - r * -q == 1
    G = compose(F, U)
    assert G[0] == -1 and G[1] % 3 == 0 and G[2] % 3 == 0
    # move the shift to |h| ≤ 1: replacing (r, s) by (r, s) + t(−p, −q) sends u ↦ u + tv
    mo = PK.monic_order(list(G))
    h = mo['u_shift']
    if h:
        t = -h
        U = ((-p, r + t * -p), (-q, s + t * -q))
        G = compose(F, U)
        mo = PK.monic_order(list(G))
    return U, G, mo


def pull(U, x):
    """`U⁻¹ x` for `det U = 1`."""
    (al, be), (ga, de) = U
    return (de * x[0] - be * x[1], -ga * x[0] + al * x[1])


def main(cmax=2_000_000):
    eqs = json.loads((ROOT / 'receipts' / 'positive_k_next.json').read_text())['equations']
    certified = set()
    rows = []
    nonmonic = [e for e in eqs if e['monic_order'] is None]
    for e in nonmonic:
        F = tuple(e['form'])
        reps = [tuple(r) for r in e['known_representations']]
        row = {'k': e['k'], 'form': list(F), 'leading': F[0], 'known_representations': [list(r) for r in reps]}
        if not reps:
            row['status'] = 'no_witness'
            rows.append(row)
            continue
        # every recorded witness gives a normalization; keep the cheapest by (slab, |coefficients|)
        best = None
        for rep in reps:
            U, G, mo = normalize(F, rep)
            entry = {'k': e['k'], 'form': list(G), 'monic_order': mo,
                     'known_representations': [list(pull(U, r)) for r in reps]}
            for r in entry['known_representations']:
                assert cubic(G, *r) == 1
            c = S.classify(entry, certified, cmax)
            c.update({'witness': list(rep), 'U': [list(U[0]), list(U[1])], 'G': list(G)})
            key = (c.get('slab_elements') or 10 ** 18, sum(abs(x) for x in G))
            if best is None or key < best[0]:
                best = (key, c)
        c = best[1]
        row.update({k: v for k, v in c.items() if k not in ('k', 'form', 'known_representations')})
        row['G_representations'] = c['known_representations']
        rows.append(row)
    tally = {}
    for r in rows:
        tally[r['status']] = tally.get(r['status'], 0) + 1
    out = {'scope': 'witness-based monic normalization of the nonmonic positive-k sources; a search, '
                    'not a proof (statuses as in rank_one_blockers.json)',
           'unit_search_cmax': cmax,
           'summary': {'nonmonic_sources': len(rows), 'with_witness': sum(r['status'] != 'no_witness' for r in rows),
                       'by_status': dict(sorted(tally.items()))},
           'sources': rows}
    (ROOT / 'receipts' / 'witness_monic.json').write_text(json.dumps(out, indent=1) + '\n')
    return out


if __name__ == '__main__':
    s = main(*(int(a) for a in sys.argv[1:]))['summary']
    print(json.dumps(s))
