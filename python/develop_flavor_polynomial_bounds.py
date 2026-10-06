"""Certify existing flavor trials without redoing the concurrent mechanism scan."""
from pathlib import Path
from fractions import Fraction as Q
from math import pi
import hashlib
import json
import sys
from perfectpower import polyalg as P
from perfectpower.flavor_polynomial_bounds import (
    bubble_shape_bracket, positive_halfline, verify_positive_halfline,
    verify_rational_bound, rational_absolute_budget, verify_absolute_budget)

ROOT = Path(__file__).resolve().parents[1]


def build():
    source = ROOT/'receipts/flavor_cosmology/tree_decay.json'
    raw = source.read_bytes()
    old = json.loads(raw)
    records = []
    for candidate in old['candidates']:
        bracket = bubble_shape_bracket(candidate['radial_polynomials'], candidate['bubble']['shape'])
        assert verify_rational_bound(bracket)
        records.append({'rank': candidate['rank'], 'certificate': bracket,
                        'action_interval': [pi*pi*float(Q(bracket[k])) for k in ('lower_bound','upper_bound')]})
    best = min(records, key=lambda r: Q(r['certificate']['upper_bound']))
    radial = old['candidates'][best['rank']]['radial_polynomials']
    T, U = [P.poly(Q(c) for c in radial[k]) for k in ('kinetic_polynomial','potential_polynomial')]
    delta = P.poly(Q(c) for c in old['completion']['kinetic_increase_polynomial'])
    positivity = {'source_kinetic': positive_halfline(T), 'mediator_kinetic_increase': positive_halfline(delta)}
    assert all(verify_positive_halfline(c) for c in positivity.values())
    # A uniform EFT-error envelope; deliberately rounded upward exactly.
    budget = Q(361,10**7)
    kinetic_budget = rational_absolute_budget(delta,T,budget)
    assert verify_absolute_budget(kinetic_budget)
    lifted = []
    for row in old['completion']['mass_scan']:
        factor = Q(row['kinetic_increase_factor'])
        polynomials = {'kinetic_polynomial': P.add(T,P.scale(delta,factor)), 'potential_polynomial': U}
        bracket = bubble_shape_bracket(polynomials, row['bubble']['shape'])
        assert verify_rational_bound(bracket)
        ratio = [Q(bracket['lower_bound'])/Q(best['certificate']['upper_bound']),
                 Q(bracket['upper_bound'])/Q(best['certificate']['lower_bound'])]
        assert ratio[0] > 1
        lifted.append({'mediator_mass': row['mediator_mass'], 'certificate': bracket,
                       'action_interval': [pi*pi*float(Q(bracket[k])) for k in ('lower_bound','upper_bound')],
                       'certified_infimum_ratio_interval': list(map(str,ratio)),
                       'display_ratio_interval': list(map(float,ratio))})
    baseline = records[-1]['certificate']
    improvement = [Q(baseline['lower_bound'])/Q(best['certificate']['upper_bound']),
                   Q(baseline['upper_bound'])/Q(best['certificate']['lower_bound'])]
    return {'schema':'pp-flavor-continuous-certification/1',
            'input_sha256':hashlib.sha256(raw).hexdigest(),
            'baseline_commit':'2a971d018fa8b87f3dc1d57678cd73d60a01cfae',
            'source_candidates':records, 'best_retained_upper_bound_rank':best['rank'],
            'mediator_lifts':lifted, 'kinetic_order_certificates':positivity,
            'uniform_kinetic_relative_error_certificate':kinetic_budget,
            'uniform_M10_action_ratio_upper':str((1+budget)**2),
            'uniform_all_mass_envelope':'For every M>0 and every admissible shape: 1<S_M(L)/S_source(L)<[1+(10/M)^2*(361/10000000)]^2. Consequently the same non-strict envelope holds for their infima. This fixes the EFT couplings and follows the same Gaussian valley; it is not a bound on transverse paths or quantum corrections.',
            'original_to_best_infimum_ratio_interval':list(map(str,improvement)),
            'display_improvement_interval':list(map(float,improvement)),
            'all_mass_statement':'On this fixed-EFT Gaussian valley, T_M=T_source+(10/M)^2*delta with delta(L)>0 for every L>=0. At every admissible shape the action strictly increases as M decreases. Its infimum is therefore nondecreasing; the listed mass pairs have strictly separated certified infimum intervals.',
            'proof':'N=T^2, D=-2U. Exact Sturm signed remainder replay proves N-bD>0 on the entire real halfline. For D>0 this gives N/D>b; the exact retained rational witness supplies an upper bound. No finite search range or approximate root matching enters the certificate.',
            'relative_bracket_width':'1/10000000000',
            'scope':'Global infimum bounds within each supplied compact-profile/path family only. The complete field-space bounce, exact stationary vacua, full algebraic group tensors, quantum corrections and lifetime remain uncertified.',
            'formal_verification':False}


def verify_report(result, raw):
    """Replay certificates and bind them to the original path polynomials."""
    try:
        if result['schema'] != 'pp-flavor-continuous-certification/1' or result['formal_verification'] is not False:
            return False
        if result['input_sha256'] != hashlib.sha256(raw).hexdigest():
            return False
        old = json.loads(raw)
        records = result['source_candidates']
        if [r['rank'] for r in records] != [c['rank'] for c in old['candidates']]:
            return False
        def linked(certificate,T,U,witness):
            return (verify_rational_bound(certificate)
                    and P.poly(Q(c) for c in certificate['numerator']) == P.mul(T,T)
                    and P.poly(Q(c) for c in certificate['denominator']) == P.scale(U,-2)
                    and Q(certificate['witness']) == Q(witness))
        for row, candidate in zip(records,old['candidates']):
            radial = candidate['radial_polynomials']
            T,U = [P.poly(Q(c) for c in radial[k]) for k in ('kinetic_polynomial','potential_polynomial')]
            if not linked(row['certificate'],T,U,candidate['bubble']['shape']):
                return False
        best = min(records,key=lambda r:Q(r['certificate']['upper_bound']))
        if result['best_retained_upper_bound_rank'] != best['rank']:
            return False
        radial = next(c for c in old['candidates'] if c['rank']==best['rank'])['radial_polynomials']
        T,U = [P.poly(Q(c) for c in radial[k]) for k in ('kinetic_polynomial','potential_polynomial')]
        delta = P.poly(Q(c) for c in old['completion']['kinetic_increase_polynomial'])
        for key,p in [('source_kinetic',T),('mediator_kinetic_increase',delta)]:
            c=result['kinetic_order_certificates'][key]
            if not verify_positive_halfline(c) or P.poly(Q(v) for v in c['coefficients']) != p:
                return False
        c=result['uniform_kinetic_relative_error_certificate']
        if not verify_absolute_budget(c) or P.poly(Q(v) for v in c['numerator']) != delta or P.poly(Q(v) for v in c['denominator']) != T:
            return False
        if Q(result['uniform_M10_action_ratio_upper']) != (1+Q(c['budget']))**2:
            return False
        if len(result['mediator_lifts']) != len(old['completion']['mass_scan']):
            return False
        for row, supplied in zip(result['mediator_lifts'],old['completion']['mass_scan']):
            c=row['certificate'];factor=Q(supplied['kinetic_increase_factor'])
            if row['mediator_mass'] != supplied['mediator_mass'] or factor != (Q(10)/Q(row['mediator_mass']))**2:
                return False
            if not linked(c,P.add(T,P.scale(delta,factor)),U,supplied['bubble']['shape']):
                return False
            expected=[Q(c['lower_bound'])/Q(best['certificate']['upper_bound']),Q(c['upper_bound'])/Q(best['certificate']['lower_bound'])]
            if list(map(Q,row['certified_infimum_ratio_interval'])) != expected or expected[0] <= 1:
                return False
        baseline=records[-1]['certificate']
        expected=[Q(baseline['lower_bound'])/Q(best['certificate']['upper_bound']),Q(baseline['upper_bound'])/Q(best['certificate']['lower_bound'])]
        return list(map(Q,result['original_to_best_infimum_ratio_interval'])) == expected
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,StopIteration):
        return False


if __name__ == '__main__':
    import argparse
    sys.set_int_max_str_digits(0)
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify',action='store_true',help='replay the persisted receipt without certificate discovery')
    args=parser.parse_args()
    output = ROOT/'receipts/flavor_cosmology/polynomial_bounds.json'
    if args.verify:
        ok=verify_report(json.loads(output.read_text()),(ROOT/'receipts/flavor_cosmology/tree_decay.json').read_bytes())
        print(json.dumps({'discovery_free_replay':ok}))
        raise SystemExit(0 if ok else 1)
    result = build()
    assert verify_report(result,(ROOT/'receipts/flavor_cosmology/tree_decay.json').read_bytes())
    output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'certificates':len(result['source_candidates'])+len(result['mediator_lifts'])+3,
                      'improvement':result['display_improvement_interval'],
                      'mass_ratios':[(r['mediator_mass'],r['display_ratio_interval']) for r in result['mediator_lifts']]}))
