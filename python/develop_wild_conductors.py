"""Replay the N41 wild-conductor receipt.

    python develop_wild_conductors.py                    # every section
    python develop_wild_conductors.py --section elliptic # one section

Receipt: receipts/curve_structure/wild_conductors.json

Sections
  identity   the GL_2(F_3) character identity behind the p=2 Swan route, over every 2-subgroup
  elliptic   Galois-route conductor exponents at 2 and 3 (tame part from j/twist/Serre-Tate, Swan from
             torsion permutation conductors; ramification-filtration replay on a subset) against
             PARI elllocalred, and Ogg's formula f = v(Delta_min) - m + 1 from our Tate algorithm and
             from PARI's own Kodaira data
  genus2_odd genus-two conductor exponents at p=3, 5 (and tame controls at 3, 5, 7) from the inertia
             image of the splitting field, wild included, against PARI genus2red
  genus2_two genus-two split Jacobians y^2=g(x^2) and Mobius images: exponent at 2 from the Galois
             route of E1, E2, against the functional equation of L(C, s) (PARI lfungenus2 with
             conductor 2^k N_odd and lfuncheckfeq); PARI genus2red returns -1 at 2
  survey     the functional-equation oracle on generic genus-two curves at 2 (oracle only; no
             method of this module applies)
All sampling is seeded; no timings are written, so reruns are byte-identical.
"""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts' / 'curve_structure' / 'wild_conductors.json'
FEQ_OK = -30     # accept the functional equation at this accuracy or better
FEQ_BAD = -20    # a wrong conductor is expected to be worse than this


def _g2_exponent(P, c, p):
    from perfectpower.wild_conductors import _pol
    r = P.genus2red(_pol(P, c), p)
    fa = r[1]
    for i in range(int(P.matsize(fa)[0])):
        if int(fa[i, 0]) == p:
            return int(fa[i, 1])
    return 0


def _odd_conductor(P, c):
    from perfectpower.wild_conductors import _pol
    N = int(P.genus2red(_pol(P, c))[0])
    while N % 2 == 0:
        N //= 2
    return N


def _hist(rows, key):
    h = {}
    for r in rows:
        k = key(r)
        h[k] = h.get(k, 0) + 1
    return dict(sorted(h.items()))


# ------------------------------------------------------------- identity
def identity_section():
    mats = [m for m in itertools.product(range(3), repeat=4) if (m[0] * m[3] - m[1] * m[2]) % 3]

    def mul(a, b):
        return ((a[0] * b[0] + a[1] * b[2]) % 3, (a[0] * b[1] + a[1] * b[3]) % 3,
                (a[2] * b[0] + a[3] * b[2]) % 3, (a[2] * b[1] + a[3] * b[3]) % 3)
    I = (1, 0, 0, 1)

    def order(m):
        k, x = 1, m
        while x != I:
            x, k = mul(x, m), k + 1
        return k
    two = [m for m in mats if order(m) in (1, 2, 4, 8, 16)]
    pts = [v for v in itertools.product(range(3), repeat=2) if v != (0, 0)]

    def act(m, v):
        return ((m[0] * v[0] + m[1] * v[1]) % 3, (m[2] * v[0] + m[3] * v[1]) % 3)

    def line(v):
        return min(v, ((-v[0]) % 3, (-v[1]) % 3))

    def close(gens):
        S, fr = {I}, [I]
        while fr:
            nx = []
            for x in fr:
                for g in gens:
                    y = mul(x, g)
                    if y not in S:
                        S.add(y)
                        nx.append(y)
            fr = nx
        return frozenset(S)
    groups = {close([a, b]) for a in two for b in two}
    groups = {G for G in groups if len(G) & (len(G) - 1) == 0}
    fails = 0
    for G in groups:
        fix = sum(all(act(m, v) == v for m in G) for v in pts)
        d = {0: 0, 2: 1, 8: 2}[fix]
        o8 = len({frozenset(act(m, v) for m in G) for v in pts})
        o4 = len({frozenset(line(act(m, v)) for m in G) for v in pts})
        fails += 2 * (2 - d) != (8 - o8) - (4 - o4)
    if fails:
        raise AssertionError('GL_2(F_3) identity fails')
    return dict(statement='2(2 - dim W^H) = (8 - #H-orbits on W-0) - (4 - #H-orbits on P(W)) for W=F_3^2',
                two_subgroups_checked=len(groups), sylow_order=max(len(G) for G in groups), failures=fails)


# ------------------------------------------------------------- elliptic
def _elliptic_sample(seed, count):
    rng = random.Random(seed)
    out = []
    while len(out) < count:
        a = [rng.randint(-2, 2), rng.randint(-6, 6), rng.randint(-3, 3), rng.randint(-40, 40), rng.randint(-80, 80)]
        mode = rng.random()
        if mode < 0.5:
            p = rng.choice([2, 3])
            for k in range(5):
                if rng.random() < 0.45:
                    a[k] *= p ** rng.randint(1, (1, 2, 3, 4, 6)[k])
        if mode > 0.85:
            a[0] = a[2] = 0
        out.append(a)
    return out


def elliptic_section(P, count=1600, filtration_every=8):
    from perfectpower.wild_conductors import elliptic_conductor_galois, ogg_exponent, pari_kodaira_symbol
    from perfectpower.dyadic_reduction import tate
    rows, bad, n_filtration, examples = [], [], 0, []
    for idx, a in enumerate(_elliptic_sample(20261009, count)):
        E = P.ellinit(a)
        if len(E) == 0 or E[11] == 0:
            continue
        for p in (2, 3):
            lr = P.elllocalred(E, p)
            fp = int(lr[0])
            if fp == 0:
                continue
            do_f = (len(rows) % filtration_every == 0)
            r = elliptic_conductor_galois(a, p, P, filtration=do_f)
            t = tate(a, p)
            kod_pari = pari_kodaira_symbol(lr[1])
            vmin_pari = int(P.valuation(P.ellminimalmodel(E)[11], p))
            ogg_pari = ogg_exponent(kod_pari, vmin_pari)
            ogg_ours = ogg_exponent(t['kodaira'], t['minimal_discriminant_valuation'])
            if do_f and r.get('swan_filtration') is not None:
                n_filtration += 1
            row = dict(a=a, p=p, kodaira=t['kodaira'], f_pari=fp, f_galois=r['conductor_exponent'], tame=r['tame'],
                       swan=r['swan'], ogg_tate=ogg_ours, ogg_pari=ogg_pari, swan_tate=t['swan'],
                       kind=r['tame_data']['kind'])
            if do_f and r.get('swan_filtration'):
                row['swan_filtration'] = r['swan_filtration']['swan']
                row['torsion_field_degree'] = r['swan_filtration']['field_degree']
            rows.append(row)
            if len({fp, r['conductor_exponent'], ogg_ours, ogg_pari, t['conductor_exponent']}) != 1 or t['swan'] != r['swan']:
                bad.append(row)
            if r['swan'] >= (4 if p == 2 else 2) and len(examples) < 12:
                examples.append(row)
    out = dict(curves=count, local_reductions=len(rows), disagreements=len(bad), disagreement_rows=bad[:20],
               filtration_replays=n_filtration,
               by_prime={str(p): dict(reductions=sum(r['p'] == p for r in rows),
                                      wild=sum(r['p'] == p and r['swan'] > 0 for r in rows),
                                      swan_histogram=_hist([r for r in rows if r['p'] == p], lambda r: 'swan=%d' % r['swan']),
                                      kodaira_histogram=_hist([r for r in rows if r['p'] == p],
                                                              lambda r: r['kodaira'] if r['kodaira'] in ('I0*', 'II', 'III', 'IV', 'II*', 'III*', 'IV*')
                                                              else ('In*' if r['kodaira'].endswith('*') else 'In')),
                                      conductor_histogram=_hist([r for r in rows if r['p'] == p], lambda r: 'f=%d' % r['f_pari']))
                         for p in (2, 3)},
               wild_examples=examples,
               rows_sha256=hashlib.sha256(json.dumps(rows).encode()).hexdigest())
    return out


# ------------------------------------------------------------- genus two at odd p
def _g2_odd_sample(seed, count):
    from sympy import symbols, Poly, prod
    x = symbols('x')
    rng = random.Random(seed)
    out, seen = [], set()

    def eis(p, deg):
        # x^deg + p*(...) with constant p*unit: totally ramified of degree deg
        c = [p * rng.randint(-3, 3) for _ in range(deg)]
        c[0] = p * rng.choice([1, 2, -1, -2, 4, 5, 7])
        return sum(ci * x ** i for i, ci in enumerate(c)) + x ** deg

    def rnd(deg):
        return sum(rng.randint(-5, 5) * x ** i for i in range(deg)) + x ** deg
    while len(out) < count:
        p = rng.choice([3, 3, 3, 5, 5, 7])
        wild_target = p in (3, 5) and rng.random() < 0.8
        if p == 3:
            pattern = rng.choice([(3, 3), (3, 2, 1), (3, 1, 1, 1), (3, 1, 1), (3, 2), (4, 2), (6,), (3, 3)])
        elif p == 5:
            pattern = rng.choice([(5,), (5, 1), (4, 1), (4, 2), (2, 2, 1, 1)])
        else:
            pattern = rng.choice([(3, 3), (3, 2, 1), (4, 1), (2, 2, 2)])
        facs = []
        for d in pattern:
            if d == 6:
                facs.append(x ** 6 + p * rng.randint(-3, 3) * x ** 3 + p * rng.choice([1, 2, -1, 4]))
            elif d == 5 and p == 5 and wild_target and rng.random() < 0.7:
                # small Galois groups: binomials (F20) and Dickson quintics x^5-5x^3+5x-a (D5)
                if rng.random() < 0.5:
                    f = x ** 5 - rng.choice([2, 3, 5, 10, 15, 20, 7, 12, 50, 75]) * rng.choice([1, -1])
                else:
                    f = x ** 5 - 5 * x ** 3 + 5 * x - rng.choice([1, 3, 4, 6, 7, 9, 11, 13])
                f = f.subs(x, x - rng.randint(-3, 3))
                facs.append(f)
            elif d == p and wild_target and rng.random() < 0.85:
                f = eis(p, d)
                if rng.random() < 0.3:
                    f = f.subs(x, x - rng.randint(-2, 2))
                facs.append(f)
            elif d == 4 and wild_target and p == 3 and rng.random() < 0.6:
                facs.append(x ** 4 + 3 * rng.randint(-2, 2) * x + 3 * rng.choice([1, 2, -1]))
            elif d == 1:
                facs.append(x - rng.randint(-9, 9) * rng.choice([1, 1, p]))
            else:
                facs.append(rnd(d))
        # optional nearby copy of a factor to create deeper clusters
        if rng.random() < 0.2 and pattern[0] == 3 and len(pattern) > 1 and pattern[1] == 3:
            facs[1] = facs[0].subs(x, x - p ** rng.randint(1, 2) * rng.choice([1, 2]))
        lead = rng.choice([1, 1, 1, 2, p])
        f = Poly(lead * prod(facs), x)
        c = [int(v) for v in reversed(f.all_coeffs())]
        if rng.random() < 0.25:
            from perfectpower.wild_conductors import mobius_sextic
            m = rng.choice([(1, 0, p, 1), (p, 1, 0, 1), (1, 1, 0, 1), (0, 1, 1, 0), (2, 1, 1, 1)])
            c = mobius_sextic(c + [0] * (7 - len(c)), m)
        key = (tuple(c), p)
        if key in seen or len(c) - 1 not in (5, 6):
            continue
        seen.add(key)
        out.append((c, p))
    return out


def genus2_odd_section(P, count=700, max_degree=72):
    from perfectpower.wild_conductors import curve_conductor_galois, _pol
    rows, bad, skipped, failed = [], [], 0, []
    for c, p in _g2_odd_sample(77001, count):
        if P.poldisc(_pol(P, c)) == 0:
            continue
        try:
            r = curve_conductor_galois(c, p, P, max_degree=max_degree)
        except Exception as ex:  # recorded, never silently dropped
            failed.append(dict(f=c, p=p, error=repr(ex)[:160]))
            continue
        if r is None:
            skipped += 1
            continue
        ref = _g2_exponent(P, c, p)
        row = dict(f=c, p=p, splitting_degree=r['splitting_degree'], e=r['e'], wild=r['wild'],
                   filtration_orders=r['filtration_orders'], tame_part=r['tame_part'], swan=r['swan'],
                   abelian_invariants=r['abelian_invariants'], toric_invariants=r['toric_invariants'],
                   wild_translations=r['wild_translations'], conductor_exponent=r['conductor_exponent'],
                   naive_multiplicity_conductor=r['naive_multiplicity_conductor'],
                   pari_genus2red=ref)
        rows.append(row)
        if ref != r['conductor_exponent']:
            bad.append(row)
    wild = [r for r in rows if r['swan'] > 0]
    out = dict(sampled=count, compared=len(rows), disagreements=len(bad), disagreement_rows=bad,
               skipped_splitting_degree_above=dict(bound=max_degree, count=skipped),
               failures=failed,
               ablation_fixed_points_counted_once=dict(
                   note='Lefschetz with every wild fixed point counted once instead of with multiplicity 3, 2',
                   disagreements_with_genus2red=sum(r['naive_multiplicity_conductor'] != str(r['pari_genus2red']) for r in rows),
                   non_integral=sum('/' in r['naive_multiplicity_conductor'] for r in rows)),
               wild=dict(count=len(wild), by_prime=_hist(wild, lambda r: str(r['p'])),
                         swan_histogram=_hist(wild, lambda r: '%d:swan=%d' % (r['p'], r['swan'])),
                         with_wild_translations=sum(r['wild_translations'] > 0 for r in wild),
                         conductor_histogram=_hist(wild, lambda r: '%d:n=%d' % (r['p'], r['conductor_exponent']))),
               tame_controls=dict(count=len(rows) - len(wild), by_prime=_hist([r for r in rows if r['swan'] == 0], lambda r: str(r['p']))),
               examples=[r for r in wild if r['wild_translations']][:15],
               rows_sha256=hashlib.sha256(json.dumps(rows).encode()).hexdigest())
    return out


# ------------------------------------------------------------- genus two at 2 (split Jacobians)
def genus2_two_section(P, count=300, neighbours_every=5, mobius_every=4, max_conductor=8 * 10 ** 6):
    from perfectpower.wild_conductors import (bielliptic_conductor_galois, analytic_exponent_check, mobius_sextic, _pol,
                                              bielliptic_factors, elliptic_euler_factor_2, poly_mul, _integral_ainvs)
    from perfectpower.dyadic_reduction import bielliptic_reduction
    rng = random.Random(31337)
    rows, bad, skipped_big, tate_bad = [], [], 0, []
    seen = set()
    attempts = 0
    while len(rows) < count and attempts < 20000:
        attempts += 1
        g = [rng.randint(-4, 4), rng.randint(-4, 4), rng.randint(-4, 4), rng.choice([1, 1, -1, 2, 3, -2, 4])]
        if rng.random() < 0.4:
            k = rng.randrange(4)
            g[k] *= 2 ** rng.randint(1, 3)
        if not g[0] or tuple(g) in seen:
            continue
        seen.add(tuple(g))
        f = [g[0], 0, g[1], 0, g[2], 0, g[3]]
        if P.poldisc(_pol(P, f)) == 0:
            continue
        b = bielliptic_conductor_galois(g, 2, P)
        t = bielliptic_reduction(g, 2)
        k0 = b['conductor_exponent']
        N = _odd_conductor(P, f)
        if N * 2 ** (k0 + 1) > max_conductor:
            skipped_big += 1
            continue
        E1, E2 = bielliptic_factors(g)
        F2 = poly_mul(elliptic_euler_factor_2(_integral_ainvs(E1), P), elliptic_euler_factor_2(_integral_ainvs(E2), P))
        feq = {str(k0): analytic_exponent_check(f, N, k0, P, euler2=F2)}
        n = len(rows)
        if n % neighbours_every == 0:
            for k in (k0 - 1, k0 + 1):
                if k >= 0:
                    feq[str(k)] = analytic_exponent_check(f, N, k, P, euler2=F2)
        row = dict(g=g, f=f, E1_tame=b['E1']['tame'], E1_swan=b['E1']['swan'], E2_tame=b['E2']['tame'], E2_swan=b['E2']['swan'],
                   exponent_galois=k0, exponent_tate=t['conductor_exponent'], odd_conductor=N, euler_factor_2=F2, feq=feq,
                   genus2red_at_2=_g2_exponent(P, f, 2))
        if n % mobius_every == 0:
            m = rng.choice([(1, 1, 1, 2), (2, 1, 1, 1), (1, 2, 0, 1), (3, 1, 2, 1), (1, 0, 2, 1), (0, 1, 1, 1)])
            fm = mobius_sextic(f, m)
            row['mobius'] = dict(m=m, f=fm, feq=analytic_exponent_check(fm, N, k0, P, euler2=F2), genus2red_at_2=_g2_exponent(P, fm, 2))
        rows.append(row)
        if t['conductor_exponent'] != k0:
            tate_bad.append(row)
        ok = feq[str(k0)] <= FEQ_OK and all(v > FEQ_BAD for k, v in feq.items() if k != str(k0))
        if 'mobius' in row:
            ok = ok and row['mobius']['feq'] <= FEQ_OK
        if not ok:
            bad.append(row)
    out = dict(compared=len(rows), skipped_conductor_above=dict(bound=max_conductor, count=skipped_big),
               galois_vs_tate_disagreements=len(tate_bad),
               functional_equation_failures=len(bad), failure_rows=bad,
               euler_factor_2_nontrivial=sum(r['euler_factor_2'] != [1] for r in rows),
               neighbour_checks=sum(len(r['feq']) > 1 for r in rows), mobius_checks=sum('mobius' in r for r in rows),
               worst_accepted_feq=max(r['feq'][str(r['exponent_galois'])] for r in rows),
               best_rejected_neighbour=min([v for r in rows for k, v in r['feq'].items() if k != str(r['exponent_galois'])] or [0]),
               genus2red_values_at_2=sorted({r['genus2red_at_2'] for r in rows}),
               exponent_histogram=_hist(rows, lambda r: 'n2=%02d' % r['exponent_galois']),
               swan_histogram=_hist(rows, lambda r: 'swan=%d' % (r['E1_swan'] + r['E2_swan'])),
               rows=rows)
    return out


def survey_section(P, count=30, max_conductor=2 * 10 ** 6):
    from perfectpower.wild_conductors import analytic_exponent_check, _pol
    rng = random.Random(4049)
    rows, tried = [], 0
    while len(rows) < count and tried < 2000:
        tried += 1
        deg = rng.choice([5, 6])
        c = [rng.randint(-3, 3) for _ in range(deg)] + [rng.choice([1, 1, -1, 2])]
        if P.poldisc(_pol(P, c)) == 0:
            continue
        if _g2_exponent(P, c, 2) == 0:
            continue
        N = _odd_conductor(P, c)
        hits = []
        for k in range(0, 21):
            if N * 2 ** k > max_conductor:
                break
            e = analytic_exponent_check(c, N, k, P)
            if e <= FEQ_OK:
                hits.append([k, e])
        if N * 2 ** 2 > max_conductor:
            continue
        rows.append(dict(f=c, odd_conductor=N, feq_hits=hits, max_k_scanned=k))
    return dict(note='oracle only: exponents of generic curves at 2 where none of the routes here applies; '
                     'lfungenus2 uses Euler factor 1 at 2, which is wrong when dim V^I > 0 at 2, so a curve '
                     'without a hit is not evidence against anything',
                curves=len(rows), with_unique_hit=sum(len(r['feq_hits']) == 1 for r in rows),
                with_no_hit_in_range=sum(not r['feq_hits'] for r in rows),
                exponent_histogram=_hist([r for r in rows if len(r['feq_hits']) == 1], lambda r: 'n2=%02d' % r['feq_hits'][0][0]),
                rows=rows)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--section', choices=['identity', 'elliptic', 'genus2_odd', 'genus2_two', 'survey', 'all'], default='all')
    args = ap.parse_args()
    from perfectpower.wild_conductors import pari, SCHEMA
    P = pari()
    P.allocatemem(1500 * 10 ** 6)
    P.default('realprecision', 38)
    data = json.loads(OUT.read_text()) if OUT.exists() else {}
    data['schema'] = SCHEMA
    data['pari_version'] = str(P.version())
    sections = ['identity', 'elliptic', 'genus2_odd', 'genus2_two', 'survey'] if args.section == 'all' else [args.section]
    for s in sections:
        if s == 'identity':
            data[s] = identity_section()
        elif s == 'elliptic':
            data[s] = elliptic_section(P)
        elif s == 'genus2_odd':
            data[s] = genus2_odd_section(P)
        elif s == 'genus2_two':
            data[s] = genus2_two_section(P)
        elif s == 'survey':
            data[s] = survey_section(P)
        print('section', s, 'done', flush=True)
    order = ['schema', 'pari_version', 'identity', 'elliptic', 'genus2_odd', 'genus2_two', 'survey']
    data = {k: data[k] for k in order if k in data}
    text = json.dumps(data, indent=1) + '\n'
    OUT.write_text(text)
    print('wrote', OUT, hashlib.sha256(text.encode()).hexdigest())


if __name__ == '__main__':
    main()
