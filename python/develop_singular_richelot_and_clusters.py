"""Reproduce singular Richelot splittings and cluster stable-reduction receipts.

python develop_singular_richelot_and_clusters.py            # main receipt (exact; braid words numerical)
python develop_singular_richelot_and_clusters.py --pari     # optional PARI genus2red cross-check receipt
"""
import argparse
import itertools
import json
import random
from fractions import Fraction as Q
from pathlib import Path

from perfectpower import singular_richelot as R
from perfectpower.cluster_stable_reduction import PadicDomain, PuiseuxDomain, analyse
from perfectpower.cluster_monodromy import topological_inertia

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts' / 'curve_structure'
PRIMES = [p for p in range(3, 80) if R.is_prime(p)]

SINGULAR = {
    'even_sextic': [[-1, 0, 1], [-4, 0, 1], [-9, 0, 1]],
    'infinity_root_rational_pencil': [[-1, 2, 0], [2, -4, 3], [-3, 6, -2]],
    'weil_restriction_sqrt2_with_infinity_root': [[2, 0, 1], [0, 1, 0], [2, -4, 1]],
    'weil_restriction_sqrt_minus1': [[-1, 0, 1], [0, 1, 0], [-1, 4, 1]],
}
SMOOTH = {
    'classical': [[1, 1, 1], [3, 2, 1], [7, 3, 1]],
    'infinity_root': [[1, 1, 0], [3, 2, 1], [7, 3, 1]],
}

# p-adic genus-two examples; 'pari' is the conductor exponent printed by PARI/GP 2.17.2 genus2red
PADIC = [
    ('three_twins', 3, 1, [0, 3, 1, 4, 2, 5], 1, 2),
    ('three_twins_twisted', 3, 1, [0, 3, 1, 4, 2, 5], 3, 4),
    ('nested_triple', 5, 1, [0, 5, 25, 1, 2], 1, 2),
    ('nested_triple_twisted', 5, 1, [0, 5, 25, 1, 2], 5, 3),
    ('disjoint_twins_two_rates', 7, 1, [0, 49, 1, 344, 2], 1, 2),
    ('cotwin_like', 3, 1, [0, 1, 2, 3, 9], 1, 2),
    ('half_depth_cluster', 5, 5, [[0, 1], [0, -1], [0, 2], [0, -2], 1, 2], 1, 3),
    ('half_depth_odd_cluster', 5, 5, [[0, 1], [0, -1], [0, 2], [0, -2], 0], 1, 4),
    ('swapped_twins', 3, 3, [[0, 1], [0, -1], [9, 1], [9, -1], 1], 1, 3),
    ('swapped_triples', 3, 3, [[0, 1], [0, -1], [9, 1], [9, -1], [18, 1], [18, -1]], 1, 4),
    ('unramified_triple', 7, 3, [[0, 49], [0, -49], 0, 1, 2], 1, 0),
    ('unramified_pair_twin', 5, 2, [[1, 25], [1, -25], 0, 2, 3, 4], 5, 4),
]

H = Q(1, 2)
# Q((t)) families: roots as {exponent: coefficient}; several collisions at different rates
TADIC = [
    ('nested_rates_1_2', [{0: 0}, {1: 1}, {2: 1}, {0: 1}, {0: 2}], {0: 1}),
    ('nested_rates_1_2_twisted', [{0: 0}, {1: 1}, {2: 1}, {0: 1}, {0: 2}], {1: 1}),
    ('disjoint_twins_rates_1_2_3', [{0: 0}, {1: 1}, {0: 1}, {0: 1, 2: 1}, {0: 2}, {0: 2, 3: 1}], {0: 1}),
    ('four_at_rate_1_genus_3', [{0: 0}, {1: 1}, {1: 2}, {1: 3}, {0: 1}, {0: 2}, {0: 3}], {0: 1}),
    ('half_rate_pairs', [{H: 1}, {H: -1}, {H: 2}, {H: -2}, {0: 1}, {0: 2}], {0: 1}),
    ('half_rate_odd_cluster', [{H: 1}, {H: -1}, {H: 2}, {H: -2}, {0: 0}], {0: 1}),
    ('swapped_twins_puiseux', [{H: 1}, {H: 1, 2: 1}, {H: -1}, {H: -1, 2: 1}, {0: 1}], {0: 1}),
    ('genus_4_three_levels', [{0: 0}, {1: 1}, {3: 1}, {3: 1, 5: 1}, {0: 1}, {0: 1, 2: 1}, {0: 2}, {0: 3}, {0: 4}, {0: 5}], {0: 1}),
    ('genus_3_twisted_nest', [{0: 0}, {2: 1}, {2: 1, 3: 1}, {1: 1}, {0: 1}, {0: 1, 1: 1}, {0: 2}, {0: 3}], {1: 1}),
]


def jsonable(x):
    if isinstance(x, Q):
        return str(x)
    if isinstance(x, dict):
        return {str(k): jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    return x


def richelot_section():
    out = {}
    for name, G in SINGULAR.items():
        r = R.singular_richelot(G)
        rows = R.verify_singular_lpolys(G, PRIMES)
        if not rows or not all(x['equal'] for x in rows):
            raise AssertionError('L-polynomial mismatch in ' + name)
        out[name] = dict(splitting=r, lpoly_rows=rows, primes_checked=len(rows),
                         kinds=sorted({x['kind'] for x in rows}))
    smooth = {}
    for name, G in SMOOTH.items():
        v = R.verify_smooth_lpolys(G, PRIMES)
        if not v['target_squarefree'] or not all(x['equal'] for x in v['rows']):
            raise AssertionError('smooth Richelot replay failed')
        smooth[name] = v
    # negative control: a quadratic twist of E2 must break the identity
    G = SINGULAR['even_sextic']
    r = R.singular_richelot(G)
    E1 = [R.K(Q(c), 0, 1) for c in r['E1_cubic']]
    E2t = [R.K(Q(c) * 2 ** (3 - i), 0, 1) for i, c in enumerate(r['E2_cubic'])]  # twist by 2
    broken = []
    for p in PRIMES[:12]:
        if not R.form_squarefree_mod_p([Q(c) for c in r['sextic_form']], p):
            continue
        L1, L2 = R.elliptic_lpoly_K(E1, p, 1, False), R.elliptic_lpoly_K(E2t, p, 1, False)
        if L1 and L2:
            broken.append(dict(p=p, equal=[int(c) for c in R.pmul(L1, L2)] == R.curve_lpoly([Q(c) for c in r['sextic_form']], p, 2)))
    if all(x['equal'] for x in broken):
        raise AssertionError('negative control did not fail')
    # exhaustive box: every delta=0 squarefree triple with coefficients in {-2..2}
    vals = range(-2, 3)
    forms = [f for f in itertools.product(vals, repeat=3) if f[1] or f[2]]
    fields, count, lchecks = {}, 0, 0
    for T in itertools.combinations(forms, 3):
        Gq = [list(map(Q, g)) for g in T]
        if R.det3(Gq) or not R.binary_squarefree(R.sextic_form(Gq)):
            continue
        s = R.singular_richelot([list(g) for g in T])
        count += 1
        fields[s['field_D']] = fields.get(s['field_D'], 0) + 1
        rows = R.verify_singular_lpolys([list(g) for g in T], [3, 5, 7, 11, 13])
        if not all(x['equal'] for x in rows):
            raise AssertionError('box L-polynomial mismatch')
        lchecks += len(rows)
    # constructed sweep in quadratic fields, generic coefficients
    rng = random.Random(20261008)
    sweep = []
    for D in (1, 2, 3, 5, -1, -2, -3, -7):
        for _ in range(4):
            while True:
                u, v = Q(rng.randint(-3, 3)), Q(rng.randint(1, 3)) if D != 1 else Q(0)
                if D == 1:
                    l1 = [R.K(Q(rng.randint(-3, 3))), R.K(Q(rng.choice([1, 2])))]
                    l2 = [R.K(Q(rng.randint(-3, 3))), R.K(Q(rng.choice([0, 1, -1])))]
                else:
                    l1 = [R.K(-u, -v, D), R.K(1, 0, D)]
                    l2 = [l1[0].conj(), l1[1].conj()]
                if not (l1[1] * l2[0] - l1[0] * l2[1]):
                    continue
                G = []
                for _ in range(3):
                    a = R.K(Q(rng.randint(-3, 3)), Q(rng.randint(-2, 2)) if D != 1 else 0, D)
                    b = a.conj() if D != 1 else R.K(Q(rng.choice([-3, -2, -1, 1, 2, 3])))
                    sq1 = [l1[0] * l1[0], 2 * l1[0] * l1[1], l1[1] * l1[1]]
                    sq2 = [l2[0] * l2[0], 2 * l2[0] * l2[1], l2[1] * l2[1]]
                    G.append([a * x + b * y for x, y in zip(sq1, sq2)])
                if any(c.b for g in G for c in g):
                    raise AssertionError('construction left the rationals')
                Gq = [[c.a for c in g] for g in G]
                if R.classify_splitting(Gq) == 'singular_richelot':
                    break
            s = R.singular_richelot(Gq)
            rows = R.verify_singular_lpolys(Gq, PRIMES[:10])
            if not rows or not all(x['equal'] for x in rows):
                raise AssertionError('sweep mismatch')
            sweep.append(dict(D=D, factors=[[str(c) for c in g] for g in Gq], field_D=s['field_D'], primes_checked=len(rows)))
    return dict(examples=out, smooth_richelot_replay=smooth,
                negative_control=dict(description='E1 x (quadratic twist of E2 by 2) for the even sextic', rows=broken),
                exhaustive_box=dict(coefficients='{-2..2}, unordered triples of distinct forms', singular_squarefree_triples=count,
                                    by_field_D={str(k): v for k, v in sorted(fields.items())}, lpoly_prime_checks=lchecks,
                                    all_split_and_matched=True),
                constructed_sweep=sweep)


def cluster_section():
    padic = []
    for name, p, D, roots, c, pari in PADIC:
        a = analyse(PadicDomain(p, D), roots, c)
        if a['reduction_over_K']['conductor_exponent'] != pari:
            raise AssertionError('conductor disagrees with the recorded PARI value: ' + name)
        padic.append(dict(name=name, p=p, D=D, leading=c, pari_genus2red_conductor_exponent=pari, analysis=a))
    tadic = []
    for name, roots, c in TADIC:
        a = analyse(PuiseuxDomain(), roots, c)
        top = topological_inertia(roots, c)
        agree = (top['topological_conductor'] == a['reduction_over_K']['conductor_exponent']
                 and top['potential_toric_rank'] == a['potential_toric_rank'])
        if not agree:
            raise AssertionError('topological replay disagrees: ' + name)
        tadic.append(dict(name=name, analysis=a, braid=top, agree=agree))
    # seeded t-adic sweep: cluster formula versus braid monodromy
    rng = random.Random(8)
    D = PuiseuxDomain()
    tally, cases = {}, 0
    while cases < 120:
        n = rng.choice([5, 6, 7, 8])
        roots = set()
        while len(roots) < n:
            if rng.random() < 0.3 and len(roots) <= n - 2:
                a0, b, e, x = rng.choice([0, 1, 2]), rng.choice([1, 2, -1]), Q(rng.choice([1, 3, 5]), 2), rng.choice([0, 1])
                for sg in (1, -1):
                    r = {Q(0): Q(a0), e: Q(sg * b)}
                    if x:
                        r[Q(3)] = Q(1)
                    roots.add(D.parse(r))
            else:
                r = {}
                for e, a in ((0, rng.choice([0, 1, 2, -1, 3])), (rng.choice([1, 2, 3]), rng.choice([0, 1, -1, 2])), (rng.choice([2, 4]), rng.choice([0, 1]))):
                    r[Q(e)] = r.get(Q(e), Q(0)) + Q(a)
                roots.add(D.parse(r))
        roots = sorted(roots)[:n]
        if any(D.sigma(r) not in set(roots) for r in roots):
            continue
        c = rng.choice([{0: 1}, {1: 1}, {1: 2}, {2: -1}, {0: 3, 1: 1}])
        rs = [dict(r) for r in roots]
        a = analyse(D, rs, c)
        top = topological_inertia(rs, c)
        key = (top['topological_conductor'] == a['reduction_over_K']['conductor_exponent'],
               top['potential_toric_rank'] == a['potential_toric_rank'])
        if key != (True, True):
            raise AssertionError('sweep disagreement at %r' % (rs,))
        k = 'genus%d_conductor%d_order%d' % (a['genus'], top['topological_conductor'], top['semisimple_order'])
        tally[k] = tally.get(k, 0) + 1
        cases += 1
    # p-adic internal sweep: DDMM semistability criterion versus the graph action (asserted inside analyse)
    rng = random.Random(9)
    pstat = {}
    for _ in range(600):
        p = rng.choice([3, 5, 7, 11, 13])
        mode = rng.choice(['rational', 'ramified', 'unramified'])
        Dd = 1 if mode == 'rational' else (p if mode == 'ramified' else next(d for d in (2, 3, 5, 6, 7, 10, 11) if d % p and pow(d, (p - 1) // 2, p) == p - 1))
        n = rng.choice([5, 6, 7, 8, 9, 10])
        roots = set()
        if Dd != 1:
            for _ in range(rng.choice([1, 2])):
                a0, b = rng.choice([0, 1]) + rng.choice([0, 1]) * p ** rng.randint(1, 3), rng.choice([1, 2]) * Q(p) ** rng.randint(-1, 2)
                roots.add((Q(a0), b))
                roots.add((Q(a0), -b))
        while len(roots) < n:
            roots.add((Q(rng.choice([0, 1, 2, -1])) + rng.choice([0, 1, -1]) * Q(p) ** rng.randint(0, 3) + rng.choice([0, 1]) * p ** rng.randint(2, 4), Q(0)))
        roots = sorted(roots)[:max(n, 3)]
        if any((a, -b) not in roots for a, b in roots):
            continue
        a = analyse(PadicDomain(p, Dd), [[x, y] for x, y in roots], rng.choice([1, p, 2, -p]))
        k = '%s_genus%d_conductor%d' % (mode, a['genus'], a['reduction_over_K']['conductor_exponent'])
        pstat[k] = pstat.get(k, 0) + 1
    return dict(padic_named=padic, tadic_named=tadic,
                tadic_braid_sweep=dict(seed=8, cases=cases, all_agree=True, tally=dict(sorted(tally.items()))),
                padic_internal_sweep=dict(seed=9, cases=sum(pstat.values()), ddmm_criterion_equals_graph_action=True,
                                          tally=dict(sorted(pstat.items()))))


def pari_section():
    import cypari2
    pari = cypari2.Pari()
    rng = random.Random(20261008)
    tally, bad, total = {}, 0, 0
    for mode in ('rational', 'unramified', 'ramified', 'moved'):
        for _ in range(250):
            p = rng.choice([3, 5, 7, 11])
            if mode == 'rational':
                D = 1
            elif mode == 'unramified':
                D = next(d for d in (2, 3, 5, 6, 7, 10, 11, 13) if d % p and pow(d, (p - 1) // 2, p) == p - 1)
            else:
                D = rng.choice([p, -p])
            n = rng.choice([5, 6])
            roots, factors = set(), []
            if mode == 'moved':
                b = rng.choice([1, 2]) * Q(p) ** rng.randint(-1, 1)
                for a0 in sorted({0, rng.choice([1, 2]) * p ** rng.randint(1, 4)} | ({rng.choice([-1, 1]) * p ** rng.randint(1, 4)} if rng.random() < 0.3 else set())):
                    roots |= {(Q(a0), b), (Q(a0), -b)}
                    factors.append('((x-(%s))^2-(%s)^2*(%d))' % (a0, b, D))
            elif D != 1:
                for _ in range(rng.choice([1, 2])):
                    a0, b = rng.choice([0, 1, 2]) + rng.choice([0, 1]) * p ** rng.randint(1, 3), rng.choice([1, 2]) * Q(p) ** rng.randint(-1, 3)
                    if (Q(a0), b) in roots:
                        continue
                    roots |= {(Q(a0), b), (Q(a0), -b)}
                    factors.append('((x-(%s))^2-(%s)^2*(%d))' % (a0, b, D))
            while len(roots) < n:
                r = rng.choice([0, 1, 2, -1]) + rng.choice([0, 1, -1, 2]) * Q(p) ** rng.randint(-1, 3) + rng.choice([0, 1]) * p ** rng.randint(2, 4)
                if (Q(r), Q(0)) in roots:
                    continue
                roots.add((Q(r), Q(0)))
                factors.append('(x-(%s))' % r)
            if len(roots) > 6:
                continue
            c = rng.choice([1, p, 2, p * p, -p])
            a = analyse(PadicDomain(p, D), [[x, y] for x, y in sorted(roots)], c)
            fa = pari.genus2red(pari('(%s)*' % c + '*'.join(factors)))[1]
            theirs = next((int(fa[1][i]) for i in range(len(fa[0])) if int(fa[0][i]) == p), 0)
            ours = a['reduction_over_K']['conductor_exponent']
            total += 1
            bad += ours != theirs
            k = '%s_conductor%d' % (mode, ours)
            tally[k] = tally.get(k, 0) + 1
    if bad:
        raise AssertionError('%d PARI disagreements' % bad)
    return dict(schema='pp-cluster-pari-crosscheck/1', engine='PARI/GP %s genus2red via cypari2' % '.'.join(map(str, pari.version())),
                seed=20261008, cases=total, disagreements=bad, tally=dict(sorted(tally.items())),
                scope='genus two, p in {3,5,7,11}, rational / unramified / ramified quadratic / Galois-swapped clusters')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--pari', action='store_true')
    args = ap.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    if args.pari:
        (OUT / 'singular_richelot_and_clusters_pari.json').write_text(json.dumps(jsonable(pari_section()), indent=1, sort_keys=True) + '\n')
        print('wrote PARI cross-check')
        return
    import time
    t0 = time.time()
    rich = richelot_section()
    print('richelot section', round(time.time() - t0, 1), 's', flush=True)
    clus = cluster_section()
    print('cluster section', round(time.time() - t0, 1), 's', flush=True)
    receipt = dict(schema='pp-singular-richelot-and-clusters/1',
                   richelot=rich, clusters=clus,
                   scope='exact identities and L-polynomial replays; braid words are read numerically on exactly bounded loops')
    (OUT / 'singular_richelot_and_clusters.json').write_text(json.dumps(jsonable(receipt), indent=1, sort_keys=True) + '\n')
    print('wrote receipt')


if __name__ == '__main__':
    main()
