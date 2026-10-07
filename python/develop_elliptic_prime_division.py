"""Complete rational division by 5 and 7 and composed 2,3,5,7 division, with independent replay."""
from pathlib import Path
import json
from perfectpower.elliptic_arithmetic import EllipticCurve, encode_point
from perfectpower.divisor_square import WorkLimit
from perfectpower import elliptic_prime_division as d
from perfectpower.elliptic_prime_division_verifier import verify_prime_division, verify_general_division

ROOT = Path(__file__).resolve().parents[1]


def summary(c):
    return {k: c[k] for k in ('target', 'points', 'method', 'root_nodes') if k in c}


def main():
    cases = []
    E11 = EllipticCurve([0, -1, 1, 0, 0]); E26 = EllipticCurve([1, -1, 1, -3, 3])
    E37 = EllipticCurve([0, 0, 1, -1, 0]); E5077 = EllipticCurve([0, 0, 1, -7, 6])
    P = E37.checked([0, 0])
    g1, g2, g3 = (E5077.checked(p) for p in ([0, 2], [1, 0], [2, 0]))
    def add(label, curve, cert, verifier):
        cases.append({'case': label, 'curve': curve.specification, **summary(cert),
                      'stage_primes': [s['prime'] for s in cert.get('stages', [])],
                      'independent_replay': verifier(cert)})
    add('11a3 five-torsion kernel', E11, d.rational_prime_division(E11, None, 5), verify_prime_division)
    add('11a3 fifths of a 5-torsion point (no Z/25)', E11, d.rational_prime_division(E11, [0, 0], 5), verify_prime_division)
    add('26b1 seven-torsion kernel', E26, d.rational_prime_division(E26, None, 7), verify_prime_division)
    add('37a1 recover P from 5P', E37, d.rational_prime_division(E37, E37.mul(P, 5), 5), verify_prime_division)
    add('37a1 recover P from 7P', E37, d.rational_prime_division(E37, E37.mul(P, 7), 7), verify_prime_division)
    add('37a1 P is not 5-divisible', E37, d.rational_prime_division(E37, [0, 0], 5), verify_prime_division)
    add('37a1 composed division of 70P', E37, d.rational_division_general(E37, E37.mul(P, 70), 70), verify_general_division)
    add('37a1 composed division of 210P', E37, d.rational_division_general(E37, E37.mul(P, 210), 210), verify_general_division)
    add('5077a1 recover g1+g2 from 5(g1+g2)', E5077, d.rational_prime_division(E5077, E5077.mul(E5077.add(g1, g2), 5), 5), verify_prime_division)
    add('5077a1 g1+5g2 is not 5-divisible', E5077, d.rational_prime_division(E5077, E5077.add(g1, E5077.mul(g2, 5)), 5), verify_prime_division)
    add('5077a1 recover g3 from 7 g3', E5077, d.rational_prime_division(E5077, E5077.mul(g3, 7), 7), verify_prime_division)
    add('26b1 composed 35-division of the identity', E26, d.rational_division_general(E26, None, 35), verify_general_division)
    budgets = []
    for label, fn in (('node budget', lambda: d.rational_division_general(E37, E37.mul(P, 210), 210, node_limit=50)),
                      ('bit budget', lambda: d.rational_prime_division(EllipticCurve([0, 0, 0, -123456789, 987654321]), None, 7, bit_limit=128)),
                      ('branch budget', lambda: d.rational_division_general(E11, None, 25, branch_limit=4))):
        try:
            fn(); budgets.append({'case': label, 'exhausted': False})
        except WorkLimit as e:
            budgets.append({'case': label, 'exhausted': True, 'message': str(e)})
    out = {'cases': cases, 'budget_exhaustion': budgets,
           'all_replayed': all(c['independent_replay'] for c in cases),
           'method': 'Producer: y-free short-model division recurrence; replay: Silverman b-invariant recurrence in the original x, Sturm root certificates replayed without search, group-law checks of every point.',
           'scope': 'Complete rational fibres of [5], [7] and products of 2,3,5,7 up to 420 on the given curves within the stated budgets. A complete fibre is not a Mordell-Weil basis or a saturation index; no Lean execution is claimed.'}
    path = ROOT/'receipts/elliptic_composed_division/prime_division.json'
    path.write_text(json.dumps(out, indent=1, sort_keys=True)+'\n')
    for c in cases: print(c['case'], c['points'], c.get('method'), c['independent_replay'])
    print(budgets)


if __name__ == '__main__':
    main()
