"""Replay the N41 (extension-field and dyadic reduction) and N42 (irregular Stokes) receipts.

    python develop_dyadic_reduction_and_stokes.py            # all three receipts
    python develop_dyadic_reduction_and_stokes.py --section stokes

Receipts (receipts/curve_structure/):
  tame_extension_clusters.json   roots in tame extension fields, Frobenius on clusters and
                                 sheets, Tamagawa numbers, tame conductors; PARI cross-checks
  dyadic_reduction.json          Tate's algorithm at 2 and 3, genus-one Jacobians, Swan
                                 conductors, genus-two good-reduction certificates and the
                                 bielliptic conductor at 2; PARI cross-checks
  irregular_stokes.json          formal normal forms, certified Kummer/Bessel/Airy Stokes
                                 matrices, numerical late-term and Borel-Pade routes, cyclic
                                 relation
All sampling is seeded; outputs contain no timings, so reruns are byte-identical.
"""
from pathlib import Path
import argparse
import hashlib
import json
import random
from fractions import Fraction as Q

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'receipts' / 'curve_structure'


def _pari():
    import cypari2
    P = cypari2.Pari()
    P.allocatemem(512 * 10 ** 6)
    return P


def _pol(P, c):
    return P('Pol([%s])' % ','.join(str(x) for x in reversed(c)))


def _g2_exponent(P, c, p):
    r = P.genus2red(_pol(P, c), p)
    fa = r[1]
    for i in range(int(P.matsize(fa)[0])):
        if int(fa[i, 0]) == p:
            return int(fa[i, 1])
    return 0


def _write(name, obj):
    text = json.dumps(obj, indent=1, sort_keys=False) + '\n'
    (OUT / name).write_text(text)
    return hashlib.sha256(text.encode()).hexdigest()


def _poly_from_factors(factors, lead=1):
    from sympy import symbols, Poly, prod
    x = symbols('x')
    f = Poly(lead * prod(eval(s, {'x': x}) for s in factors), x)
    return [int(c) for c in reversed(f.all_coeffs())]


# ------------------------------------------------------------- N41 (i): tame extension fields
def tame_section(P):
    from perfectpower.tame_cluster_frobenius import analyse_curve, extension_tamagawa, swan_conductor_roots
    from perfectpower.semistable_tamagawa import rational_root_tamagawa
    out = dict(schema='pp-tame-extension-clusters/1', pari_version=str(P.version()), named=[], cross_checks={})
    named = [
        ('twin conjugate over Q_9, elliptic (nonsplit I2)', ['x**2-18', 'x-1'], 1, 3),
        ('twin conjugate over Q_9, twisted by 2', ['x**2-18', 'x-1'], 2, 3),
        ('Frobenius 2-cycle of twins centred at 1+-sqrt2, genus 2', ['((x-1)**2-7)**2-8*(x-1)**2', 'x', 'x+1'], 1, 3),
        ('the same, twisted by 2', ['((x-1)**2-7)**2-8*(x-1)**2', 'x', 'x+1'], 2, 3),
        ('twin in ramified Q_5(sqrt 5), elliptic', ['x**2-125', 'x-1', 'x-2'], 1, 5),
        ('cube roots of 7 (e=3), genus 2', ['x**3-7', 'x**3-2'], 1, 7),
        ('fourth roots of 5 (e=4), genus 2', ['x**4-5', 'x'], 1, 5),
        ('sixth roots of 7 (e=6), genus 2', ['x**6-7'], 1, 7),
        ('unramified quintic roots, genus 2', ['x**5+2'], 1, 7),
    ]
    for label, factors, lead, p in named:
        c = _poly_from_factors(factors, lead)
        if P.poldisc(_pol(P, c)) == 0:
            raise AssertionError('named curve not squarefree: ' + label)
        a, _, _ = analyse_curve(c, p)
        row = dict(label=label, p=p, coefficients=c, splitting_field=a['splitting_field'], genus=a['genus'],
                   frobenius_root_permutation=a['frobenius_root_permutation'],
                   inertia_root_permutation=a['inertia_root_permutation'],
                   frobenius_cluster_permutation=a['frobenius_cluster_permutation'],
                   inertia_cluster_permutation=a['inertia_cluster_permutation'],
                   clusters=a['clusters'], conductor_exponent=a['conductor_exponent'],
                   tame_inertia={k: a['tame_inertia'][k] for k in ('order', 'abelian_part_invariants', 'toric_rank',
                                                                  'potential_abelian_dimension', 'potential_toric_rank',
                                                                  'semistable_over_K')},
                   semistable_over_K=a['semistable_over_K'])
        if a['genus'] == 2:
            row['pari_genus2red_exponent'] = _g2_exponent(P, c, p)
        else:
            E = P.ellinit(P.ellfromeqn(P('y^2-(%s)' % _pol(P, c))))
            lr = P.elllocalred(E, p)
            row['pari_elllocalred'] = dict(f=int(lr[0]), kodaira=int(lr[1]), c=int(lr[3]))
        if a['semistable_over_K']:
            t = extension_tamagawa(c, p)
            row.update(tamagawa_number=t['tamagawa_number'], geometric_component_order=t['geometric_component_order'],
                       invariant_factors=t['component_group']['invariant_factors'],
                       frobenius_sheet_signs=t['frobenius_sheet_signs'], frobenius_orbit_records=t['frobenius_orbit_records'])
            if a['genus'] == 2:
                r = P.genus2red(_pol(P, c), p)
                row['pari_genus2red_group'] = [int(x) for x in r[3][2][1]]
        ref = row.get('pari_genus2red_exponent', row.get('pari_elllocalred', {}).get('f'))
        if ref != a['conductor_exponent']:
            raise AssertionError('named conductor disagrees with PARI: ' + label)
        if 'pari_elllocalred' in row and 'tamagawa_number' in row and row['pari_elllocalred']['c'] != row['tamagawa_number']:
            raise AssertionError('named Tamagawa disagrees with PARI: ' + label)
        out['named'].append(row)
    # (1) conductor exponents, genus two, p in {3,5,7}
    rng = random.Random(20261008)
    rows, stats = [], {}
    for _ in range(260):
        p = rng.choice([3, 5, 7])
        deg = rng.choice([5, 6])
        c = [rng.randint(-30, 30) for _ in range(deg)] + [rng.choice([1, 1, 2, p])]
        for k in range(len(c) - 1):
            if rng.random() < 0.4:
                c[k] *= p ** rng.randint(1, 2)
        if P.poldisc(_pol(P, c)) == 0:
            continue
        try:
            a, _, _ = analyse_curve(c, p)
        except ArithmeticError:
            stats['no_tame_splitting_field_in_bounds'] = stats.get('no_tame_splitting_field_in_bounds', 0) + 1
            continue
        ref = _g2_exponent(P, c, p)
        e = a['splitting_field']['e']
        stats['e=%d' % e] = stats.get('e=%d' % e, 0) + 1
        rows.append([p, c, a['splitting_field']['f'], e, a['conductor_exponent'], ref])
    bad = [r for r in rows if r[4] != r[5]]
    if bad:
        raise AssertionError('genus-two conductor disagreements: %r' % bad[:3])
    out['cross_checks']['genus2_conductor_vs_genus2red'] = dict(curves=len(rows), disagreements=0, by_ramification=stats,
                                                                 columns='p, coefficients, f, e, ours, PARI', rows=rows)
    # (2) Tamagawa numbers, genus one (cubic and quartic), against elllocalred
    rng = random.Random(77)
    rows, skipped = [], 0
    for _ in range(420):
        p = rng.choice([3, 5, 7, 11])
        deg = rng.choice([3, 4])
        c = [rng.randint(-20, 20) for _ in range(deg)] + [rng.choice([1, 1, 2, 3])]
        for k in range(len(c) - 1):
            if rng.random() < 0.5:
                c[k] *= p ** rng.randint(1, 3)
        if P.poldisc(_pol(P, c)) == 0:
            continue
        try:
            t = extension_tamagawa(c, p)
        except (ValueError, ArithmeticError):
            skipped += 1
            continue
        E = P.ellinit(P.ellfromeqn(P('y^2-(%s)' % _pol(P, c))))
        lr = P.elllocalred(E, p)
        rows.append([p, c, t['splitting_field']['f'], t['splitting_field']['e'], t['conductor_exponent'], t['tamagawa_number'],
                     int(lr[0]), int(lr[3]), int(lr[1])])
    bad = [r for r in rows if (r[4], r[5]) != (r[6], r[7])]
    if bad:
        raise AssertionError('genus-one Tamagawa disagreements: %r' % bad[:3])
    ext = sum(1 for r in rows if r[2] > 1 or r[3] > 1)
    out['cross_checks']['genus1_tamagawa_vs_elllocalred'] = dict(
        curves=len(rows), with_irrational_roots=ext, disagreements=0, skipped_not_semistable_or_untame=skipped,
        columns='p, coefficients, f, e, our f_p, our c_p, PARI f_p, PARI c_p, PARI Kodaira code', rows=rows)
    # (3) geometric component groups, genus two, against genus2red
    rng = random.Random(4242)
    rows, skipped = [], 0
    for _ in range(320):
        p = rng.choice([3, 5, 7])
        factors, deg, target = [], 0, rng.choice([5, 6])
        while deg < target:
            a0 = rng.randint(-6, 6)
            kind = rng.random()
            if target - deg >= 2 and kind < 0.35:
                k = rng.randint(1, 3)
                D = rng.randint(2, 30)
                factors.append('(x-(%d))**2-%d' % (a0, D * p ** (2 * k)))
                deg += 2
            elif target - deg >= 2 and kind < 0.5:
                D = next(d for d in range(2, 40) if pow(d, (p - 1) // 2, p) == p - 1)
                factors.append('(x-(%d))**2-%d' % (a0, D))
                deg += 2
            else:
                factors.append('x-(%d)' % (a0 + p ** rng.randint(0, 2) * rng.randint(-3, 3)))
                deg += 1
        c = _poly_from_factors(factors, rng.choice([1, 1, 2, 3, p]))
        if P.poldisc(_pol(P, c)) == 0:
            continue
        try:
            t = extension_tamagawa(c, p)
        except (ValueError, ArithmeticError):
            skipped += 1
            continue
        r = P.genus2red(_pol(P, c), p)
        grp = sorted(int(x) for x in r[3][2][1] if int(x) > 1)
        rows.append([p, c, t['splitting_field']['f'], t['splitting_field']['e'], t['component_group']['invariant_factors'],
                     grp, t['tamagawa_number']])
    bad = [r for r in rows if sorted(r[4]) != r[5]]
    if bad:
        raise AssertionError('component group disagreements: %r' % bad[:3])
    out['cross_checks']['genus2_component_group_vs_genus2red'] = dict(
        curves=len(rows), with_irrational_roots=sum(1 for r in rows if r[2] > 1 or r[3] > 1), disagreements=0,
        skipped_not_semistable=skipped,
        columns='p, coefficients, f, e, our invariant factors, PARI group (>1), our Frobenius-fixed order', rows=rows,
        note='PARI reports the geometric group only; the Frobenius-fixed order is checked against elllocalred in genus one')
    # (4) regression: rational roots against the existing odd-prime adapter
    reg = []
    for p in [3, 5, 7]:
        for d in range(1, 4):
            for lead in [1, 2]:
                roots = [0, p ** d, 1]
                old = rational_root_tamagawa(p, roots, lead)
                c = _poly_from_factors(['x-(%d)' % r for r in roots], lead)
                new = extension_tamagawa(c, p)
                reg.append([p, roots, lead, old['tamagawa_number'], new['tamagawa_number']])
    old = rational_root_tamagawa(3, [0, 3, 1, 4, 2, 5], 2)
    new = extension_tamagawa(_poly_from_factors(['x-(%d)' % r for r in [0, 3, 1, 4, 2, 5]], 2), 3)
    reg.append([3, [0, 3, 1, 4, 2, 5], 2, old['tamagawa_number'], new['tamagawa_number']])
    if any(r[3] != r[4] for r in reg):
        raise AssertionError('regression against rational_root_tamagawa failed')
    out['cross_checks']['rational_root_regression'] = dict(curves=len(reg), rows=reg)
    # (5) wild part for p odd: Swan conductor of the roots against Tate (genus one, p=3)
    from perfectpower.dyadic_reduction import genus_one_reduction
    rng = random.Random(33)
    rows = []
    for _ in range(160):
        c = [rng.randint(-9, 9) * 3 ** rng.randint(0, 2) for _ in range(3)] + [1]
        if P.poldisc(_pol(P, c)) == 0:
            continue
        m = genus_one_reduction(c, 3)
        sw = swan_conductor_roots(c, 3, P)['swan']
        rows.append([c, sw, m['swan'], m['kodaira']])
    bad = [r for r in rows if r[1] != r[2]]
    if bad:
        raise AssertionError('Swan disagreement: %r' % bad[:3])
    out['cross_checks']['swan_roots_vs_tate_p3_genus1'] = dict(curves=len(rows), wild=sum(1 for r in rows if r[1]),
                                                                disagreements=0, rows=rows)
    rng = random.Random(55)
    rows = []
    for _ in range(120):
        p = rng.choice([3, 5])
        c = [rng.randint(-9, 9) * p ** rng.randint(0, 2) for _ in range(5)] + [1]
        if P.poldisc(_pol(P, c)) == 0:
            continue
        sw = swan_conductor_roots(c, p, P)['swan']
        n = _g2_exponent(P, c, p)
        rows.append([p, c, sw, n])
    bad = [r for r in rows if not 0 <= r[3] - r[2] <= 4]
    if bad:
        raise AssertionError('Swan exceeds the PARI conductor: %r' % bad[:3])
    out['cross_checks']['swan_roots_vs_genus2red_bound'] = dict(
        curves=len(rows), wild=sum(1 for r in rows if r[2]), violations=0,
        check='0 <= n_PARI - swan <= 2g (consistency only: the tame part in the wild case is not computed here)', rows=rows)
    return _write('tame_extension_clusters.json', out)


# ------------------------------------------------------------- N41 (ii): p = 2
def dyadic_section(P):
    from perfectpower.dyadic_reduction import (tate, kodaira_pari_code, genus_one_reduction,
                                               genus2_good_reduction_certificate, bielliptic_reduction)
    from perfectpower.tame_cluster_frobenius import root_galois_data, IndexDomain, tame_inertia
    from perfectpower.cluster_stable_reduction import cluster_picture
    out = dict(schema='pp-dyadic-reduction/1', pari_version=str(P.version()), named={}, cross_checks={})
    # Tate at 2, 3, 5 against elllocalred
    rng = random.Random(2026)
    kinds, n, rows_bad = {}, 0, []
    swan_hist = {}
    for _ in range(4000):
        a = [rng.randint(-3, 3) for _ in range(5)]
        if rng.random() < 0.5:
            q = rng.choice([2, 3])
            a = [x * q ** rng.randint(0, 3) for x in a]
        E = P.ellinit(a)
        if len(E) == 0:
            continue
        for p in (2, 3, 5):
            m = tate(a, p)
            lr = P.elllocalred(E, p)
            n += 1
            kod = m['kodaira']
            if kod not in ('I0', 'I0*', 'II', 'III', 'IV', 'II*', 'III*', 'IV*'):
                kod = 'In*' if kod.endswith('*') else 'In'
            key = '%d:%s' % (p, kod)
            kinds[key] = kinds.get(key, 0) + 1
            if m['swan']:
                k2 = '%d:swan=%d' % (p, m['swan'])
                swan_hist[k2] = swan_hist.get(k2, 0) + 1
            if (int(lr[0]), int(lr[1]), int(lr[3])) != (m['conductor_exponent'], kodaira_pari_code(m['kodaira']), m['tamagawa']):
                rows_bad.append([a, p])
    if rows_bad:
        raise AssertionError('Tate disagreements: %r' % rows_bad[:3])
    out['cross_checks']['tate_vs_elllocalred'] = dict(local_reductions=n, disagreements=0, types=dict(sorted(kinds.items())),
                                                      swan_histogram=dict(sorted(swan_hist.items())))
    # genus one hyperelliptic models (cubic and quartic) at 2 and 3
    rng = random.Random(11)
    n, bad = 0, []
    for _ in range(500):
        c = [rng.randint(-12, 12) for _ in range(rng.choice([4, 5]))]
        if c[-1] == 0 or P.poldisc(_pol(P, c)) == 0:
            continue
        E = P.ellinit(P.ellfromeqn(P('y^2-(%s)' % _pol(P, c))))
        for p in (2, 3):
            m = genus_one_reduction(c, p)
            lr = P.elllocalred(E, p)
            n += 1
            if (int(lr[0]), int(lr[1]), int(lr[3])) != (m['conductor_exponent'], kodaira_pari_code(m['kodaira']), m['tamagawa']):
                bad.append([c, p])
    if bad:
        raise AssertionError('genus-one model disagreements: %r' % bad[:3])
    out['cross_checks']['genus1_hyperelliptic_vs_ellfromeqn'] = dict(local_reductions=n, disagreements=0,
                                                                     model='cubic: scaling; quartic: Y^2=X^3-27IX-27J')
    # genus two good-reduction certificates at 2
    rng = random.Random(1)
    stats = dict(certified_and_pari_good=0, certified_but_pari_bad=0, pari_good_not_certified=0, both_bad=0)
    examples = []
    for _ in range(1500):
        Qc = [rng.randint(-2, 2) for _ in range(4)]
        Pc = [rng.randint(-3, 3) for _ in range(7)]
        if rng.random() < 0.5:
            Pc[6] = 0
        f = [0] * 7
        for i in range(4):
            for j in range(4):
                f[i + j] += Qc[i] * Qc[j]
        f = [f[k] + 4 * Pc[k] for k in range(7)]
        while f and f[-1] == 0:
            f.pop()
        if len(f) - 1 not in (5, 6) or P.poldisc(_pol(P, f)) == 0:
            continue
        good = _g2_exponent(P, f, 2) == 0
        ct = genus2_good_reduction_certificate(f)
        key = ('certified_and_pari_good' if good else 'certified_but_pari_bad') if ct else ('pari_good_not_certified' if good else 'both_bad')
        stats[key] += 1
        if ct and len(examples) < 12:
            examples.append(dict(f=f, certificate=ct))
    if stats['certified_but_pari_bad']:
        raise AssertionError('good-reduction certificate contradicted by genus2red')
    out['cross_checks']['genus2_good_reduction_at_2'] = dict(stats, examples=examples,
        family='f=Q^2+4P with random small Q (deg<=3), P (deg<=6); genus2red omits 2 from the conductor exactly for good reduction')
    # bielliptic genus two: conductor exponents at 2 (PARI genus2red does not compute them) and at 3 (checked)
    rng = random.Random(9)
    rows3, rows2 = [], []
    for _ in range(420):
        g = [rng.randint(-10, 10) for _ in range(3)] + [rng.choice([1, 1, 2, -1, 4])]
        if g[0] == 0:
            continue
        f = [g[0], 0, g[1], 0, g[2], 0, g[3]]
        if P.poldisc(_pol(P, f)) == 0:
            continue
        b3 = bielliptic_reduction(g, 3)
        rows3.append([g, b3['conductor_exponent'], _g2_exponent(P, f, 3)])
        b2 = bielliptic_reduction(g, 2)
        rows2.append([g, b2['E1']['kodaira'], b2['E2']['kodaira'], b2['conductor_exponent'], b2['swan'], _g2_exponent(P, f, 2)])
    bad = [r for r in rows3 if r[1] != r[2]]
    if bad:
        raise AssertionError('bielliptic conductor at 3 disagrees with genus2red: %r' % bad[:3])
    hist = {}
    for r in rows2:
        hist[str(r[3])] = hist.get(str(r[3]), 0) + 1
    good_agree = all((r[3] == 0) == (r[5] == 0) for r in rows2)
    if not good_agree:
        raise AssertionError('bielliptic good/bad at 2 disagrees with genus2red')
    out['cross_checks']['bielliptic_conductor'] = dict(
        curves=len(rows3), at_3_agree_with_genus2red=len(rows3), at_2_exponent_histogram=dict(sorted(hist.items(), key=lambda kv: int(kv[0]))),
        at_2_pari_returns=sorted(set(r[5] for r in rows2)),
        note='PARI 2.17 genus2red reports exponent -1 at 2 for bad reduction (not computed); good/bad at 2 agrees on every curve',
        rows_at_2=rows2)
    # cluster diagnostic at 2: the odd-p tame formula applied at p=2 versus Tate (genus one)
    rng = random.Random(5)
    agree = disagree = 0
    sample = []
    for _ in range(400):
        c = [rng.randint(-9, 9) for _ in range(3)] + [1]
        if P.poldisc(_pol(P, c)) == 0:
            continue
        try:
            data = root_galois_data(c, 2)
        except ArithmeticError:
            continue
        pic = cluster_picture(IndexDomain(2, data), list(range(3)), 1)
        naive = tame_inertia(pic, data['inertia'], data['field'].e)['conductor_exponent']
        true = genus_one_reduction(c, 2)['conductor_exponent']
        if naive == true:
            agree += 1
        else:
            disagree += 1
            if len(sample) < 10:
                sample.append(dict(f=c, odd_p_formula=naive, tate=true))
    out['cross_checks']['odd_p_cluster_formula_at_2'] = dict(
        tame_split_cubics=agree + disagree, agree=agree, disagree=disagree, sample_disagreements=sample,
        conclusion='the odd-p cluster conductor is not valid at 2; it is reported only as a diagnostic')
    # named examples
    out['named']['y2+y=x5'] = dict(f=[1, 0, 0, 0, 0, 4], certificate=genus2_good_reduction_certificate([1, 0, 0, 0, 0, 4]),
                                   pari_conductor=int(P.genus2red(_pol(P, [1, 0, 0, 0, 0, 4]))[0]))
    out['named']['249a'] = dict(f=[1, 4, 4, 2, 0, 0, 1], certificate=genus2_good_reduction_certificate([1, 4, 4, 2, 0, 0, 1]),
                                pari_conductor=int(P.genus2red(_pol(P, [1, 4, 4, 2, 0, 0, 1]))[0]))
    out['named']['y2=x3+2 at 2'] = tate([0, 0, 0, 0, 2], 2)
    out['named']['y2=x3-x at 2'] = tate([0, 0, 0, -1, 0], 2)
    out['named']['y2=x6+x2+1 bielliptic at 2'] = bielliptic_reduction([1, 1, 0, 1], 2)
    for k in ('y2+y=x5', '249a'):
        if out['named'][k]['certificate'] is None or out['named'][k]['pari_conductor'] % 2 == 0:
            raise AssertionError('named good-reduction example failed: ' + k)
    return _write('dyadic_reduction.json', out)


# ------------------------------------------------------------- N42: Stokes
def stokes_section():
    import mpmath as mp
    from perfectpower.irregular_stokes import (formal_normal_form, kummer_system, certified_kummer_stokes,
                                               late_term_stokes, borel_pade_stokes, numerical_cyclic_relation)
    mp.mp.dps = 40
    out = dict(schema='pp-irregular-stokes-receipt/1', certified=[], numerical=[], formal=[])

    def s(x):
        return mp.nstr(x, 18)
    cases = [('Kummer a=1/3 b=3/4', '1/3', '3/4'), ('Kummer a=2/5 b=7/3', '2/5', '7/3'),
             ('Kummer a=-1/4 b=1/2', '-1/4', '1/2'), ('Kummer a=1/2 b=1 (Bessel nu=0, integer b)', '1/2', '1'),
             ('Bessel nu=1/3 = Airy', '5/6', '5/3'), ('Bessel nu=1/4', '3/4', '3/2'), ('Bessel nu=2/5', '9/10', '9/5'),
             ('Kummer a=-1 b=1/2 (polynomial U: s_pi=0)', '-1', '1/2')]
    for label, a, b in cases:
        rec, raw = certified_kummer_stokes(a, b)
        if not rec['certified']:
            raise AssertionError('Stokes certification failed: ' + label)
        ch = formal_normal_form(kummer_system(a, b), order=60)
        # classical 2F0 coefficients replayed exactly from the formal normal form (first row of P F)
        from sympy import Rational, rf, factorial
        aa, bb = Rational(a), Rational(b)
        F = ch['coefficients']
        ok = all(Rational(F[k][0][0]) + Rational(F[k][1][0]) == rf(aa, k) * rf(1 + aa - bb, k) * (-1) ** k / factorial(k)
                 and Rational(F[k][0][1]) + Rational(F[k][1][1]) == rf(bb - aa, k) * rf(1 - aa, k) / factorial(k) for k in range(0, 40))
        if not ok:
            raise AssertionError('formal coefficients differ from the classical 2F0 series: ' + label)
        lt = late_term_stokes(ch)
        bp = borel_pade_stokes(ch, R=6)
        cs0 = mp.mpc(raw['S0'][0, 1].real.mid().str(30, radius=False), raw['S0'][0, 1].imag.mid().str(30, radius=False))
        csp = mp.mpc(raw['S_pi'][1, 0].real.mid().str(30, radius=False), raw['S_pi'][1, 0].imag.mid().str(30, radius=False))
        rec['formal_matches_classical_2F0'] = True
        rec['numerical'] = dict(late_term_s0=s(lt['s0']), late_term_s_pi=s(lt['s_pi']),
                                borel_pade_s0=s(bp['s0']), borel_pade_s_pi=s(bp['s_pi']),
                                late_term_error=mp.nstr(max(abs(lt['s0'] - cs0), abs(lt['s_pi'] - csp)), 3),
                                borel_pade_error=mp.nstr(max(abs(bp['s0'] - cs0), abs(bp['s_pi'] - csp)), 3))
        if max(abs(lt['s0'] - cs0), abs(lt['s_pi'] - csp)) > 1e-8 or max(abs(bp['s0'] - cs0), abs(bp['s_pi'] - csp)) > 1e-8:
            raise AssertionError('numerical Stokes route disagrees with certified value: ' + label)
        rec['label'] = label
        out['certified'].append(rec)
    # numerical-only system with an A_2 term (not hypergeometric)
    A = [[[0, 0], [0, 1]], [['1/3', 1], [1, '-1/2']], [[0, '1/5'], ['2/7', 0]]]
    ch = formal_normal_form(A, order=60)
    lt = late_term_stokes(ch)
    cyc = numerical_cyclic_relation(A, ch)
    agree = max(abs(lt['s0'] - cyc['s0']), abs(lt['s_pi'] - cyc['s_pi']))
    if agree > 1e-8 or cyc['max_difference'] > 1e-8:
        raise AssertionError('generic numerical Stokes routes disagree')
    out['numerical'].append(dict(system=A, eigenvalues=ch['eigenvalues'], formal_exponents=ch['formal_exponents'],
                                 late_term_s0=s(lt['s0']), late_term_s_pi=s(lt['s_pi']),
                                 borel_pade_s0=s(cyc['s0']), borel_pade_s_pi=s(cyc['s_pi']),
                                 route_difference=mp.nstr(agree, 3),
                                 monodromy_numerical_transport=[[s(cyc['monodromy'][i, j]) for j in range(2)] for i in range(2)],
                                 cyclic_product=[[s(cyc['product'][i, j]) for j in range(2)] for i in range(2)],
                                 cyclic_relation_residual=mp.nstr(cyc['max_difference'], 3),
                                 status='numerical (mpmath 40 digits), not certified'))
    # formal normal forms in rank 3 and 4
    for A in ([[[0, 1, 0], [0, 1, 1], [0, 0, 3]], [['1/2', 0, 1], [1, '-1/3', 0], [0, 2, '1/5']], [[0, 1, 0], [0, 0, 1], [1, 0, 0]]],
              [[[-1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 2, 0], [1, 0, 0, 5]], [[0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1], ['1/7', 0, 0, 0]]]):
        ch = formal_normal_form(A, order=30)
        out['formal'].append(dict(system=A, eigenvalues=ch['eigenvalues'], eigenframe=ch['eigenframe'],
                                  formal_exponents=ch['formal_exponents'], identity_checked=ch['identity_checked'],
                                  first_coefficients=ch['coefficients'][:4],
                                  coefficient_sha256=hashlib.sha256(json.dumps(ch['coefficients']).encode()).hexdigest()))
    return _write('irregular_stokes.json', out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--section', choices=['tame', 'dyadic', 'stokes', 'all'], default='all')
    args = ap.parse_args()
    P = None
    if args.section in ('tame', 'dyadic', 'all'):
        P = _pari()
    if args.section in ('tame', 'all'):
        print('PASS tame extension clusters', tame_section(P), flush=True)
    if args.section in ('dyadic', 'all'):
        print('PASS dyadic reduction', dyadic_section(P), flush=True)
    if args.section in ('stokes', 'all'):
        print('PASS irregular Stokes', stokes_section(), flush=True)


if __name__ == '__main__':
    main()
