"""Interval-certified O(3)/O(4) bounce actions at the wall_nucleation benchmarks (N40, part 2).

Writes receipts/flavor_cosmology/wall_bounce_intervals.json. Every interval is an Arb
enclosure written with outward decimal rounding; floating values are only compared.
"""
from decimal import Decimal, ROUND_FLOOR, ROUND_CEILING, getcontext
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import sys
import time

from flint import arb
from perfectpower import wall_bounce_intervals as wb
from perfectpower import wall_nucleation as wn

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'receipts/flavor_cosmology/wall_nucleation.json'
OUT = ROOT/'receipts/flavor_cosmology/wall_bounce_intervals.json'
DIGITS = 16
getcontext().prec = 60


def frac(x):
    m, e = x.man_exp()
    return Fraction(int(m))*Fraction(2)**int(e)


def interval(x, digits=DIGITS):
    """[lo, hi] decimal strings with outward rounding of the Arb ball x."""
    lo, hi = frac(x.lower()), frac(x.upper())

    def dec(q, mode):
        d = Decimal(q.numerator)/Decimal(q.denominator)
        if d == 0:
            return '0'
        exp = d.adjusted() - digits + 1
        return str(d.quantize(Decimal(1).scaleb(exp), rounding=mode))
    return [dec(lo, ROUND_FLOOR), dec(hi, ROUND_CEILING)]


def inside(value, iv):
    return Decimal(iv[0]) <= Decimal(repr(value)) <= Decimal(iv[1])


def rel_dev(value, x):
    """(value-mid)/mid of a float against an enclosure (floating summary only)."""
    m = float(x.mid())
    return (value - m)/m


QUOTED = {3: '62.148', 4: '179.36'}


def quoted_ok(x, q):
    """Both ends of the enclosure round (half-even) to the quoted decimal."""
    e = Decimal(q).as_tuple().exponent
    lo, hi = (Decimal(s) for s in interval(x, 30))
    return lo.quantize(Decimal(1).scaleb(e)) == hi.quantize(Decimal(1).scaleb(e)) == Decimal(q)


def strip(c):
    """JSON-ready certificate summary."""
    fam = c['family']
    return {'exists_overshoot_undershoot': c['exists'],
            'bracket_lo_class': c['lo']['status'], 'bracket_hi_class': c['hi']['status'],
            'classification_radius': [c['lo']['r'], c['hi']['r']],
            'phi0_bracket_half_width': '1e-%d' % (len(str(c['delta'].denominator)) - 1),
            'phi0_seed': c['phi0_seed'].str(30, radius=False),
            'tail_radius_R': fam.get('R'), 'tail_bound_on_int_r^{d-1}phi_prime^2': interval(fam['tail_bound'], 4)
            if 'tail_bound' in fam else None,
            'integration_steps': fam.get('steps'),
            's_virial': interval(fam['s']), 's_direct_T_plus_U': interval(fam['s_direct']),
            'virial_and_direct_overlap': bool(fam['s'].overlaps(fam['s_direct'])),
            'certified': c['certified']}


def main(cover=True):
    t0 = time.time()
    src = json.loads(SOURCE.read_text())
    model = src['declared_model']
    lam, v, c = (wb.exact(model[k]) for k in ('lam', 'v_GeV', 'thermal_c'))
    out = {'input_wall_nucleation_receipt_sha256': hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
           'method': wb.__doc__.strip().split('\n\n')[0],
           'integrator': {'precision_bits': 160, 'taylor_order': 36, 'per_step_tolerance': 1e-32,
                          'phi0_bracket_half_width': '1e-20', 'tail_start_u_below': 1e-9,
                          'covering': {'precision_bits': 96, 'taylor_order': 24}}}

    # 1. Universal cubic and the near-spinodal constants.
    cub = {}
    s_cubic = {}
    for d in (3, 4):
        cert = wb.certify_bounce(wb.cubic(), d)
        with wb._prec(160):
            s_cubic[d] = cert['s'] + 0
        cub[str(d)] = strip(cert)
        cub[str(d)]['floating_wall_nucleation'] = src['spinodal']['cubic_bounce'][str(d)]
        cub[str(d)]['floating_relative_deviation'] = rel_dev(src['spinodal']['cubic_bounce'][str(d)], s_cubic[d])
    with wb._prec(160):
        C = wb.spinodal_constants(s_cubic)
        out['cubic'] = {'potential': 'w^2/2-w^3/3, false vacuum w=0', 'rows': cub,
                        'uniqueness': 'Positive radial solution of Delta w=w-w^2 vanishing at infinity is unique '
                                      '(Kwong 1989; p=2 is subcritical for d=3,4), so the certified bounce is the '
                                      'least-action one.'}
        out['spinodal_constants'] = {}
        for d in (3, 4):
            iv = interval(C[d])
            fl = src['spinodal']['C_exact'][str(d)]
            out['spinodal_constants']['C%d' % d] = {
                'formula': 'C_d=(2*3^(1/4))^((6-d)/2) s_cubic(d)/3', 'certified': iv,
                'floating_wall_nucleation': fl, 'floating_relative_deviation': rel_dev(fl, C[d]),
                'quoted_value': QUOTED[d],
                'quoted_value_is_certified_rounding': quoted_ok(C[d], QUOTED[d])}
        print('C', {d: C[d].str(16) for d in C}, time.time() - t0, flush=True)

    # 2. Tree-potential bounces at the critical biases of wall_nucleation.
    rows = []
    for r in src['nucleation_threshold']:
        T = r['T_GeV']
        for d in (3, 4):
            rec = r['d%d' % d]['0.0']
            eps = rec['eps_star']
            pot = wb.quartic(eps)
            t1 = time.time()
            cert = wb.certify_bounce(pot, d)
            row = {'T_GeV': T, 'd': d, 'eps': eps, 'eps_exact_dyadic': True,
                   'floating_method': rec['method'], 'floating_s_star_target': rec['s_star'],
                   'floating_S_star': rec['S_star']}
            row.update(strip(cert))
            with wb._prec(160):
                s = cert['s'] + 0
                if d == 3:
                    Te = wb.exact(T)
                    vT = v*(1 - c*Te*Te/(lam*v*v)).sqrt()
                    scale = vT/(lam.sqrt()*Te)
                    S = scale*s
                    row['S_definition'] = 'S3/T=(v_T/(sqrt(lam) T)) s3, v_T=v sqrt(1-cT^2/(lam v^2)) in Arb'
                else:
                    S = s/lam
                    row['S_definition'] = 'S4=s4/lam'
                row['S_certified'] = interval(S)
                row['floating_S_star_relative_deviation'] = rel_dev(rec['S_star'], S)
                row['floating_S_star_inside'] = inside(rec['S_star'], row['S_certified'])
                if rec['method'] == 'bounce':
                    fb = wn.bounce(eps, d)['s']
                    row['floating_bounce_s_recomputed'] = fb
                    row['floating_bounce_relative_deviation'] = rel_dev(fb, s)
                else:
                    Ci = C[d]
                    asym = Ci*(wb.exact(wn.EPS_SPINODAL) - wb.exact(eps))**(arb(6 - d)/4)
                    row['near_spinodal_law_with_certified_C'] = interval(asym)
                    row['exact_over_asymptotic_law'] = interval(s/asym, 8)
            if cover and pot.t is not None:
                la = wb.certify_least_action(pot, d, cert['phi0_seed'])
                row['least_action'] = jsonable(la)
            rows.append(row)
            print(T, d, row['S_certified'], row.get('least_action', {}).get('least_action'),
                  round(time.time() - t1), flush=True)
    out['benchmarks'] = rows
    out['summary'] = {
        'all_existence_certified': all(r['certified'] for r in rows) and all(v['certified'] for v in cub.values()),
        'all_least_action_certified': all(r.get('least_action', {}).get('least_action') for r in rows),
        'floating_bounce_values_max_relative_deviation': max(abs(r['floating_bounce_relative_deviation'])
                                                             for r in rows if 'floating_bounce_relative_deviation' in r),
        'near_spinodal_rows': [{'T_GeV': r['T_GeV'], 'S_certified': r['S_certified'],
                                'floating_S_star_from_asymptotic_law': r['floating_S_star'],
                                'exact_over_asymptotic_law': r['exact_over_asymptotic_law']}
                               for r in rows if 'exact_over_asymptotic_law' in r]}
    out['not_claimed'] = [
        'Corrected (one-loop CW / thermal / two-loop) potentials: they contain log|m^2(phi)| (non-analytic inside the '
        'bounce) and spline-interpolated thermal functions; no enclosure of those bounces is given.',
        'The near-spinodal law s=C_d (eps_sp-eps)^{(6-d)/4} is asymptotic; only C_d and the exact actions at the '
        'benchmark biases are certified.',
        'The critical biases eps* themselves are floating roots; the actions are certified at those (exact dyadic) eps.',
        'Fluctuation determinant (still the declared exp(+-20) band) and the three-field sandwich factor.',
        'Least-action identification relies on the Coleman-Glaser-Martin theorem (minimiser radial, monotone, '
        'values in [f,t]) and, for the cubic, on Kwong\'s uniqueness theorem; these are cited, not re-proved.']
    OUT.write_text(json.dumps(out, indent=1, sort_keys=True) + '\n')
    print(json.dumps(out['spinodal_constants'], indent=1))
    print(json.dumps(out['summary'], indent=1))
    print('total', time.time() - t0)


def jsonable(x):
    if isinstance(x, dict):
        return {k: jsonable(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [jsonable(v) for v in x]
    if isinstance(x, Fraction):
        return str(x) if x.denominator < 10**30 else float(x)
    if isinstance(x, arb):
        return interval(x, 6)
    return x


if __name__ == '__main__':
    main(cover='--no-cover' not in sys.argv)
