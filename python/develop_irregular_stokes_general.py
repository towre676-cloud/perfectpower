"""Replay the N42 completion receipt: certified Stokes data without closed forms, repeated
leading eigenvalues and ramified irregular exponents.

    python develop_irregular_stokes_general.py

Writes receipts/curve_structure/irregular_stokes_general.json.  Every number is an Arb ball
from perfectpower.irregular_stokes_general.certified_stokes (Volterra-bounded sectorial
solutions + certified Taylor transport).  Closed forms enter only as validation targets.
Deterministic: fixed radii, precisions and paths; no timings in the output.
"""
from pathlib import Path
import hashlib
import json
import sys
from fractions import Fraction as Q

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))
OUT = ROOT / 'receipts' / 'curve_structure'

from perfectpower.irregular_stokes_general import (  # noqa: E402
    certified_stokes, birkhoff2_closed_form, balls_overlap, formal_data, op_from_ode, op_mul, turrittin_scalar,
    reduce_to_rank_one, exps_record, scalar_operator_record, _fmat, _mul, _inv, _s, SCHEMA)
from perfectpower.irregular_stokes import kummer_system, kummer_closed_forms, formal_normal_form, borel_pade_stokes  # noqa: E402


def _write(name, obj):
    text = json.dumps(obj, indent=1, sort_keys=False) + '\n'
    (OUT / name).write_text(text)
    return hashlib.sha256(text.encode()).hexdigest()


def _conj(G, mats):
    G = _fmat(G)
    Gi = _inv(G)
    return [[[str(x) for x in row] for row in _mul(_mul(G, _fmat(m)), Gi)] for m in mats]


def _require(cond, msg):
    if not cond:
        raise AssertionError(msg)


def _cert(A, R, label):
    rec, raw = certified_stokes(A, R)
    _require(rec['certified'], 'certification failed: %s R=%s %s' % (label, R, rec['checks']))
    return rec, raw


def _pair(A, R1, R2, label):
    r1, w1 = _cert(A, R1, label)
    r2, w2 = _cert(A, R2, label)
    ov = balls_overlap(w1, w2)
    _require(ov, 'independent radii disagree: ' + label)
    return r1, r2, w1, w2, ov


def _mid(x):
    import mpmath as mp
    return mp.mpc(x.real.mid().str(40, radius=False), x.imag.mid().str(40, radius=False))


def kummer_section():
    from flint import ctx
    out = []
    cases = [('1/3', '3/4'), ('2/5', '7/3'), ('-1/4', '1/2'), ('1/2', '1'), ('5/6', '5/3'), ('3/4', '3/2'),
             ('9/10', '9/5'), ('-1', '1/2')]
    for a, b in cases:
        rec, raw = _cert(kummer_system(a, b), 48, 'Kummer %s %s' % (a, b))
        s0, sp = kummer_closed_forms(a, b, prec=256)
        cf = birkhoff2_closed_form(raw['fd'], prec=256)
        c1 = bool(raw['S0'][0, 1].overlaps(s0)) and bool(raw['S_pi'][1, 0].overlaps(sp))
        c2 = all(bool(c['s0'].overlaps(s0)) and bool(c['s_pi'].overlaps(sp)) for c in cf)
        _require(c1 and c2, 'Kummer closed form not contained: %s %s' % (a, b))
        rec.update(label='Kummer a=%s b=%s' % (a, b), s0_closed_form=_s(s0), s_pi_closed_form=_s(sp),
                   contains_closed_forms=c1, kummer_map_roots_agree=c2)
        out.append(rec)
    return out


def unramified_section():
    """Distinct and repeated leading eigenvalues, no closed form (plus repeated-eigenvalue validations)."""
    import mpmath as mp
    out = []
    # (1) the 2x2 system with an A_2 term from irregular_stokes.json (numerical there)
    A = [[[0, 0], [0, 1]], [['1/3', 1], [1, '-1/2']], [[0, '1/5'], ['2/7', 0]]]
    r1, r2, w1, w2, ov = _pair(A, 40, 56, '2x2 J=2')
    old = json.loads((OUT / 'irregular_stokes.json').read_text())['numerical'][0]
    lt0, ltp = (mp.mpc(complex(old[k].replace(' ', ''))) for k in ('late_term_s0', 'late_term_s_pi'))
    d = max(abs(_mid(w2['S0'][0, 1]) - lt0), abs(_mid(w2['S_pi'][1, 0]) - ltp))
    _require(d < 1e-12, 'previous numerical values disagree')
    out.append(dict(label='2x2, A_2 term (z=0 irregular): the numerical-only system of irregular_stokes.json',
                    closed_form=None, radius_runs=[r1, r2], radii_overlap=ov,
                    previous_numerical_late_term=[old['late_term_s0'], old['late_term_s_pi']],
                    distance_to_previous_numerical=mp.nstr(d, 3)))
    # (2) 2x2 with A_2 and A_3
    A = [[[1, 2], [0, -1]], [['1/4', '1/3'], ['-1/2', '1/5']], [['1/7', 0], [1, '-1/3']], [[0, '1/6'], [0, 0]]]
    r1, r2, w1, w2, ov = _pair(A, 40, 56, '2x2 J=3')
    ch = formal_normal_form(A, order=60)
    bp = borel_pade_stokes(ch, R=8)
    d = max(abs(_mid(w2['S0'][0, 1]) - bp['s0']), abs(_mid(w2['S_pi'][1, 0]) - bp['s_pi']))
    _require(d < 1e-8, 'Borel-Pade disagrees (2x2 J=3)')
    out.append(dict(label='2x2, A_2 and A_3 terms, non-diagonal A_0 (eigenvalues -1, 1)', closed_form=None,
                    radius_runs=[r1, r2], radii_overlap=ov,
                    borel_pade_numerical=[mp.nstr(bp['s0'], 15), mp.nstr(bp['s_pi'], 15)], distance_to_borel_pade=mp.nstr(d, 3)))
    # (3) 3x3 Birkhoff (J=1) with generic residue: local exponents at 0 are algebraic of degree 3
    A = [[[-1, 0, 0], [0, 0, 0], [0, 0, 1]], [['1/3', 1, '-1/2'], ['2/5', '-1/4', 1], [1, '1/7', '1/2']]]
    r1, r2, w1, w2, ov = _pair(A, 40, 56, '3x3 J=1 a')
    out.append(dict(label='3x3 Birkhoff system A_0+A_1/z, generic A_1 (not hypergeometric)', closed_form=None,
                    radius_runs=[r1, r2], radii_overlap=ov))
    # (4) 3x3 Birkhoff with non-diagonal A_0 (eigenvalues 0,1,3)
    A = [[[0, 1, 0], [0, 1, 1], [0, 0, 3]], [['1/2', 0, 1], [1, '-1/3', 0], [0, 2, '1/5']]]
    r1, r2, w1, w2, ov = _pair(A, 36, 48, '3x3 J=1 b')
    out.append(dict(label='3x3 Birkhoff system, upper-triangular A_0 with eigenvalues 0,1,3', closed_form=None,
                    radius_runs=[r1, r2], radii_overlap=ov))
    # (5) 3x3 with z=0 irregular (J=2)
    A = [[[-1, 0, 0], [0, 0, 0], [0, 0, 1]], [['1/3', 1, '-1/2'], ['2/5', '-1/4', 1], [1, '1/7', '1/2']],
         [[0, '1/5', 0], [0, 0, '1/3'], ['1/7', 0, 0]]]
    r1, r2, w1, w2, ov = _pair(A, 40, 56, '3x3 J=2')
    out.append(dict(label='3x3 with A_2 term (z=0 irregular)', closed_form=None, radius_runs=[r1, r2], radii_overlap=ov))
    # (6) repeated eigenvalue, validation: Kummer(1/3,3/4) + scalar e^z z^{2/5}, conjugated
    a, b, c = Q(1, 3), Q(3, 4), Q(2, 5)
    A = _conj([[1, 1, 0], [0, 1, 1], [1, 0, 1]], ([[0, 1, 0], [0, 1, 0], [0, 0, 1]], [[0, 0, 0], [a, -b, 0], [0, 0, c]]))
    rec, raw = _cert(A, 40, 'Kummer+scalar')
    s0, sp = kummer_closed_forms(a, b, prec=256)
    lam = rec['eigenvalues']
    S0, Sp = raw['S0'], raw['S_pi']
    prods = {}
    for j in range(3):
        if lam[j] == '1':
            prods[j] = S0[0, j] * Sp[j, 0]
    kum = [j for j in prods if prods[j].overlaps(s0 * sp) and not prods[j].overlaps(0 * s0)]
    zero = [j for j in prods if S0[0, j].overlaps(0 * s0) and Sp[j, 0].overlaps(0 * s0)]
    _require(len(kum) == 1 and len(zero) == 1, 'Kummer+scalar block structure')
    out.append(dict(label='repeated eigenvalue 1 (validation): G(Kummer(1/3,3/4) + [1+(2/5)/z])G^-1', closed_form='Kummer product s0*s_pi',
                    radius_runs=[rec], invariant_product=_s(prods[kum[0]]), closed_form_product=_s(s0 * sp),
                    product_contains_closed_form=True, decoupled_column_vanishes=True))
    # (7) repeated eigenvalues 0 and 1, 4x4 validation: Kummer(1/3,3/4) + Kummer(2/5,7/3)
    k1, k2 = kummer_system('1/3', '3/4'), kummer_system('2/5', '7/3')
    A0 = [[0, 1, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 0, 1]]
    A1 = [[0, 0, 0, 0], [Q(1, 3), Q(-3, 4), 0, 0], [0, 0, 0, 0], [0, 0, Q(2, 5), Q(-7, 3)]]
    A = _conj([[1, 0, 1, 0], [0, 1, 0, 1], [1, 1, 0, 0], [0, 1, 1, 1]], (A0, A1))
    rec, raw = _cert(A, 40, 'Kummer+Kummer')
    S0, Sp = raw['S0'], raw['S_pi']
    lam = rec['eigenvalues']
    targets = [kummer_closed_forms('1/3', '3/4', prec=256), kummer_closed_forms('2/5', '7/3', prec=256)]
    ok = []
    for s0, sp in targets:
        hits = [(i, j) for i in range(4) for j in range(4) if lam[i] == '0' and lam[j] == '1'
                and (S0[i, j] * Sp[j, i]).overlaps(s0 * sp) and not (S0[i, j] * Sp[j, i]).overlaps(0 * s0)]
        ok.append(hits)
    _require(all(len(h) == 1 for h in ok) and ok[0] != ok[1], 'Kummer+Kummer pairing')
    out.append(dict(label='repeated eigenvalues 0,0,1,1 (validation): G(Kummer(1/3,3/4)+Kummer(2/5,7/3))G^-1',
                    closed_form='Kummer products', radius_runs=[rec],
                    matched_pairs=[list(h[0]) for h in ok],
                    products=[_s(S0[h[0][0], h[0][1]] * Sp[h[0][1], h[0][0]]) for h in ok],
                    closed_form_products=[_s(s0 * sp) for s0, sp in targets]))
    # (8) repeated eigenvalue, no closed form
    A = [[[1, 0, 0], [0, 1, 0], [0, 0, 0]], [['1/3', '1/2', 1], ['1/6', 0, '2/3'], ['1/2', 1, '1/7']]]
    r1, r2, w1, w2, ov = _pair(A, 40, 56, 'repeated generic')
    out.append(dict(label='repeated eigenvalue 1 (multiplicity 2), generic residue: no closed form', closed_form=None,
                    radius_runs=[r1, r2], radii_overlap=ov))
    return out


def _check_turrittin_vs_matrix(red, fd):
    """Turrittin exponents of z versus the matrix formal normal form in s=z^{p/q}."""
    pq = Q(red['p'], red['q'])
    ex = red['exponents']
    lead = [Q(str(e['phi'].get(Q(red['kstar']), 0))) for e in ex]
    ok = True
    for e, c in zip(ex, lead):
        i = fd['lam'].index(c)
        ok = ok and Q(str(e['rho'])) == fd['mu'][i] * pq
    return ok


def ramified_section():
    from flint import acb, ctx
    out = []

    def run(label, L, radii, expected=None, closed=True, numerical=False):
        ex = turrittin_scalar(L)
        red = reduce_to_rank_one(L, ex)
        fd = formal_data(red['A'], order=int(3 * max(radii)) + 12)
        cons = _check_turrittin_vs_matrix(red, fd)
        _require(cons, 'Turrittin exponents disagree with the matrix normal form: ' + label)
        runs, raws = [], []
        for R in radii:
            rec, raw = certified_stokes(red['A'], R, fd=fd)
            _require(rec['certified'], 'certification failed: ' + label)
            runs.append(rec)
            raws.append(raw)
        item = dict(label=label, operator_theta_form=scalar_operator_record(L), turrittin=exps_record(ex),
                    reduction=dict(q=red['q'], p=red['p'], common_factor=red['psi'], s_variable=red['s_variable'],
                                   system_in_s=[[[str(x) for x in r] for r in m] for m in red['A']]),
                    turrittin_matches_matrix_normal_form=cons, radius_runs=runs)
        if len(raws) == 2:
            item['radii_overlap'] = balls_overlap(raws[0], raws[1])
            _require(item['radii_overlap'], 'radii disagree: ' + label)
        raw = raws[-1]
        if closed:
            cf = birkhoff2_closed_form(fd, prec=256)
            okc = all(bool(raw['S0'][0, 1].overlaps(c['s0'])) and bool(raw['S_pi'][1, 0].overlaps(c['s_pi'])) for c in cf)
            _require(okc, 'Kummer-map closed form not contained: ' + label)
            item['kummer_map_closed_form'] = [dict(a=_s(c['a']), b=_s(c['b']), s0=_s(c['s0']), s_pi=_s(c['s_pi'])) for c in cf]
            item['contains_kummer_map_closed_form'] = okc
        if expected is not None:
            old = ctx.prec
            ctx.prec = 256
            try:
                e0, ep, how = expected()
            finally:
                ctx.prec = old
            oke = bool(raw['S0'][0, 1].overlaps(e0)) and bool(raw['S_pi'][1, 0].overlaps(ep))
            _require(oke, 'classical Stokes multipliers not contained: ' + label)
            item.update(classical=how, classical_s0=_s(e0), classical_s_pi=_s(ep), contains_classical=oke)
        if numerical:
            import mpmath as mp
            ch = formal_normal_form(red['A'], order=60)
            bp = borel_pade_stokes(ch, R=8)
            d = max(abs(_mid(raw['S0'][0, 1]) - bp['s0']), abs(_mid(raw['S_pi'][1, 0]) - bp['s_pi']))
            _require(d < 1e-8, 'Borel-Pade disagrees: ' + label)
            item['distance_to_borel_pade'] = mp.nstr(d, 3)
        out.append(item)
        return raw

    I = lambda: acb(0, 1)
    # Airy: w''=zw, Katz invariant 3/2, nilpotent leading term
    run('Airy w\'\'=z w (leading matrix nilpotent, exponent 3/2)', op_from_ode([{1: -1}, {}, {0: 1}]), [40, 56],
        expected=lambda: (I(), -I(), 'Ai(z)+w Ai(wz)+w^2 Ai(w^2 z)=0 gives s_0=i in the normalisation z^(-1/4)e^(-+2/3 z^(3/2)); s_pi=-i from the cyclic relation'))
    # Weber: w''=(z^2/4+a)w, exponent 2, nilpotent leading term
    for a in ('0', '1/3', '-1/4', '3/2', '1/2'):
        aa = Q(a)

        def exp_weber(aa=aa):
            from flint import arb, fmpq
            A_ = acb(arb(fmpq(aa.numerator, aa.denominator)))
            r2p = (2 * acb.pi()).sqrt()
            s0 = I() * r2p * (acb(1) / 2 - A_).rgamma()
            sp = -I() * (-acb.pi() * I() * A_).exp() * r2p * (acb(1) / 2 + A_).rgamma()
            return s0, sp, 's_0=i sqrt(2 pi)/Gamma(1/2-a) (DLMF 12.2.18 in the normalisation z^(-a-1/2)e^(-z^2/4), z^(a-1/2)e^(z^2/4)); s_pi=-i e^(-i pi a) sqrt(2 pi)/Gamma(1/2+a)'
        run('Weber w\'\'=(z^2/4+a)w, a=%s' % a, op_from_ode([{2: Q(-1, 4), 0: -aa}, {}, {0: 1}]), [96],
            expected=exp_weber)
    # repeated leading eigenvalue 1 (Jordan block) with ramified sub-exponent: w=e^z z^(-nu/2) I_nu(2 sqrt z)-type
    for nu in ('0', '1/3', '1/4', '2/5'):
        nn = Q(nu)

        def exp_bes(nn=nn):
            from flint import arb, fmpq
            c = 2 * I() * (acb.pi() * acb(arb(fmpq(nn.numerator, nn.denominator)))).cos()
            return c, -c, 's_0=2i cos(pi nu), s_pi=-2i cos(pi nu) (DLMF 10.34.2 for K_nu in the normalisation x^(-1/2)e^(-+x), x=2t)'
        run('z w\'\'+(nu+1-2z)w\'+(z-nu-2)w=0, nu=%s: A_0=[[0,1],[-1,2]] (double eigenvalue 1, Jordan), exponents z+-2z^(1/2)' % nu,
            op_from_ode([{1: 1, 0: -nn - 2}, {0: nn + 1, 1: -2}, {1: 1}]), [24], expected=exp_bes)
    # ramified, no closed form
    run('w\'\'=(z+1/(5z^2)+1/(7z^5))w: exponent 3/2, z=0 irregular, no closed form',
        op_from_ode([{1: -1, -2: Q(-1, 5), -5: Q(-1, 7)}, {}, {0: 1}]), [40, 56], closed=False, numerical=True)
    from sympy import Rational
    L3 = {(Q(0), 3): Rational(1), (Q(3), 1): Rational(-1), (Q(3), 0): Rational(1, 3), (Q(-3), 0): Rational(1, 5)}
    run('theta^3 - z^3 theta + z^3/3 + z^-3/5 (third order, exponents 0, +-2/3 z^(3/2)): no closed form', L3, [64, 80], closed=False)
    return out


def formal_section():
    from sympy import Rational
    out = []
    ops = [('hyper-Airy w\'\'\'=z w (complex leading coefficients: formal only)', op_from_ode([{1: -1}, {}, {}, {0: 1}])),
           ('mixed slopes (theta-z)(theta^2-z)', op_mul({(Q(0), 1): Rational(1), (Q(1), 0): Rational(-1)},
                                                        {(Q(0), 2): Rational(1), (Q(1), 0): Rational(-1)})),
           ('Airy', op_from_ode([{1: -1}, {}, {0: 1}])),
           ('repeated root then ramification: z w\'\'+(1-2z)w\'+(z-2)w=0', op_from_ode([{1: 1, 0: -2}, {0: 1, 1: -2}, {1: 1}])),
           ('w\'\'\'=z^2 w\'+w (slopes 0 and 2)', op_from_ode([{0: -1}, {2: -1}, {}, {0: 1}]))]
    for label, L in ops:
        out.append(dict(label=label, operator_theta_form=scalar_operator_record(L), turrittin=exps_record(turrittin_scalar(L))))
    # formal normal form with a repeated eigenvalue: identity replay and agreement with irregular_stokes in distinct cases
    fd = formal_data([[[1, 0, 0], [0, 1, 0], [0, 0, 0]], [['1/3', '1/2', 1], ['1/6', 0, '2/3'], ['1/2', 1, '1/7']]], order=40)
    out.append(dict(label='cluster formal normal form, A_0=diag(1,1,0)', eigenvalues=[str(x) for x in fd['lam']],
                    formal_exponents=[str(x) for x in fd['mu']], eigenframe=[[str(x) for x in r] for r in fd['P']],
                    identity_checked=fd['identity_checked'], first_coefficients=[[[str(x) for x in r] for r in fd['F'][k]] for k in range(1, 3)]))
    return out


def negative_controls():
    """Understate the proven Volterra bound by 10^3: some certification check must fail."""
    out = []
    systems = [('Kummer a=1/3 b=3/4', kummer_system('1/3', '3/4')),
               ('2x2 with A_2 term', [[[0, 0], [0, 1]], [['1/3', 1], [1, '-1/2']], [[0, '1/5'], ['2/7', 0]]]),
               ('3x3 Birkhoff generic', [[[-1, 0, 0], [0, 0, 0], [0, 0, 1]], [['1/3', 1, '-1/2'], ['2/5', '-1/4', 1], [1, '1/7', '1/2']]]),
               ('Airy in s=z^(3/2)', reduce_to_rank_one(op_from_ode([{1: -1}, {}, {0: 1}]))['A'])]
    for label, A in systems:
        good, _ = certified_stokes(A, 24)
        _require(good['certified'], 'control baseline')
        from perfectpower.irregular_stokes_general import formal_data, best_truncation
        fd = formal_data(A, order=84)
        eta = best_truncation(fd, 24)['eta'] / 1000
        bad, _ = certified_stokes(A, 24, fd=fd, eta_override=eta)
        failed = [k for k, v in bad['checks'].items() if not v]
        _require(failed and not bad['certified'], 'negative control not detected: ' + label)
        out.append(dict(label=label, radius='24', proven_eta=good['asymptotic_error_bound'],
                        understated_eta=bad['asymptotic_error_bound'], failed_checks=failed))
    return out


def main():
    rep = dict(schema=SCHEMA + '-receipt', scope=(
        'Certified (Arb) Stokes matrices at an irregular singular point of Poincare rank one in z or in a ramified '
        'variable s=z^(p/q) reached by an exact Turrittin reduction; real rational leading eigenvalues, '
        'repeated ones allowed with diagonalisable non-resonant residue blocks. Sectorial solutions enclosed '
        'by an explicit Volterra contraction bound; closed forms used only for validation.'))
    rep['kummer_validation'] = kummer_section()
    print('kummer', len(rep['kummer_validation']), flush=True)
    rep['unramified_without_closed_form'] = unramified_section()
    print('unramified', len(rep['unramified_without_closed_form']), flush=True)
    rep['ramified_and_repeated'] = ramified_section()
    print('ramified', len(rep['ramified_and_repeated']), flush=True)
    rep['turrittin_formal'] = formal_section()
    rep['negative_controls'] = negative_controls()
    runs = [r for sec in ('unramified_without_closed_form', 'ramified_and_repeated') for it in rep[sec] for r in it['radius_runs']]
    runs += rep['kummer_validation']
    rep['summary'] = dict(certified_runs=len(runs), all_certified=all(r['certified'] for r in runs),
                          max_ball_radius=max(r['max_ball_radius'] for r in runs),
                          largest_system=max(r['rank'] for r in runs), largest_J=max(r['J'] for r in runs))
    print('PASS irregular Stokes general', _write('irregular_stokes_general.json', rep), flush=True)


if __name__ == '__main__':
    main()
