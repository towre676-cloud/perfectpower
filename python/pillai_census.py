"""Pillai gap census: all pairs of perfect powers 1 < P < Q <= B with Q - P <= K.

A perfect power is m^e with m >= 2, e >= 2.  The search is exhaustive up to B, so every listed
set is exact *within [2, B]* (EXACT_COMPUTATION); nothing is claimed beyond B.  Pillai's
conjecture (open) says that for each k only finitely many pairs have difference k.  For fixed
exponents (a, b) finiteness is known (LeVeque/Siegel, effective by Baker), and k = 1 is settled
completely by Mihailescu's theorem (Catalan): only 9 - 8.  The census re-finds (8, 9) as a
regression check but does not claim to prove Catalan.

Method: squares are too many to list up to B = 1e18, but two squares within K of each other are
both below (K/2 + 1)^2, so square-square pairs are enumerated directly.  Every other pair contains
a non-square perfect power (about 1.0e6 of them below 1e18); for each, the squares within K are
found by isqrt and the non-square powers within K by a sorted sweep.

    python3 python/pillai_census.py [B_exponent] [K]      # default 18, 1000
Writes data/pillai_gaps.csv and receipts/pillai_census_summary.json.
"""
import csv
import json
import sys
from bisect import bisect_left, bisect_right
from collections import defaultdict
from math import isqrt
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from perfectpower.core import floor_nth_root, integer_power_root


def representations(v: int):
    """All (m, e) with m >= 2, e >= 2, m^e = v."""
    out = []
    e = 2
    while 2 ** e <= v:
        m = integer_power_root(v, e)
        if m is not None and m >= 2:
            out.append((m, e))
        e += 1
    return out


def main():
    E = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    B = 10 ** E
    # non-square perfect powers <= B (odd prime exponents suffice to generate them)
    ns = set()
    e = 3
    while 2 ** e <= B:
        top = floor_nth_root(B, e)
        for m in range(2, top + 1):
            v = m ** e
            if isqrt(v) ** 2 != v:
                ns.add(v)
        e += 1
    ns = sorted(ns)
    pairs = set()
    # square-square pairs: s^2 - r^2 <= K forces s <= K/2 + 1
    smax = K // 2 + 2
    for r in range(2, smax + 1):
        for s in range(r + 1, smax + 2):
            if s * s - r * r > K:
                break
            if s * s <= B:
                pairs.add((r * r, s * s))
    for q in ns:
        lo = max(4, q - K)
        hi = min(B, q + K)
        for s in range(max(2, isqrt(lo - 1) + 1), isqrt(hi) + 1):
            v = s * s
            if v != q:
                pairs.add((min(v, q), max(v, q)))
        for v in ns[bisect_left(ns, lo):bisect_right(ns, hi)]:
            if v != q:
                pairs.add((min(v, q), max(v, q)))
    by_k = defaultdict(list)
    for p, q in sorted(pairs):
        by_k[q - p].append((p, q))
    root = Path(__file__).resolve().parents[1]
    (root / 'data').mkdir(exist_ok=True)
    with open(root / 'data' / 'pillai_gaps.csv', 'w', newline='') as fh:
        w = csv.writer(fh, lineterminator='\n')
        w.writerow(['k', 'P', 'Q', 'P_representations', 'Q_representations', 'certification'])
        for k in sorted(by_k):
            for p, q in by_k[k]:
                w.writerow([k, p, q, ' '.join(f'{m}^{e}' for m, e in representations(p)),
                            ' '.join(f'{m}^{e}' for m, e in representations(q)),
                            f'EXACT_WITHIN_BOUND (Q <= 10^{E})'])
    assert by_k[1] == [(8, 9)], by_k[1]          # regression: Catalan/Mihailescu
    summary = {
        'B': f'10^{E}', 'K': K, 'nonsquare_powers_enumerated': len(ns), 'pairs': len(pairs),
        'k_with_no_pair': [k for k in range(1, K + 1) if k not in by_k],
        'pairs_per_k_first_30': {k: len(by_k.get(k, [])) for k in range(1, 31)},
        'largest_Q_per_k_first_30': {k: max(q for _, q in by_k[k]) for k in range(1, 31) if k in by_k},
        'k_equal_1': by_k[1],
        'note': 'exact within [2, B]; says nothing about pairs above B. Pillai conjecture open.',
    }
    (root / 'receipts' / 'pillai_census_summary.json').write_text(json.dumps(summary, indent=1) + '\n')
    print(json.dumps({x: summary[x] for x in ('B', 'K', 'nonsquare_powers_enumerated', 'pairs', 'k_equal_1')}))
    print('pairs per k:', summary['pairs_per_k_first_30'])
    print('no pair for k in', summary['k_with_no_pair'][:40])


if __name__ == '__main__':
    main()
