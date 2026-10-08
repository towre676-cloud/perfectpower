"""Reproduce the refined affine-face resolutions and the certified Legendre connection.

Writes deterministic receipts under receipts/curve_structure/.
"""
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path
from perfectpower import bernstein_boxes as B
from perfectpower import metric_boxes_refined as MR
from perfectpower import legendre_certified_connection as L
from perfectpower.curve_families import CurveFamily

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'receipts/curve_structure'
OUT.mkdir(parents=True, exist_ok=True)
BOX = [0, 1, -10**100, 10**100]


def dump(name, data):
    text = json.dumps(data, indent=1, ensure_ascii=False)+'\n'
    (OUT/name).write_text(text)
    return hashlib.sha256(text.encode()).hexdigest()


def affine_faces():
    rows, packets = [], []
    totals = dict(cases=0, originally_complete=0, originally_unresolved=0, face_only_certified_false=0,
                  face_only_certified_true=0, still_unresolved=0, integer_models_complete=0, brute_force_agree=0)
    for d, power, a, eqs in MR.corpus():
        totals['cases'] += 1
        base = B.solve_affine_faces(eqs, BOX)
        if base['complete']:
            totals['originally_complete'] += 1
            continue
        totals['originally_unresolved'] += 1
        p = MR.refine(eqs, BOX)
        assert MR.verify(p) and p['original_verified'] and not p['original_complete']
        brute = [[x, y] for x in [0, 1] for y in range(-2, 3) if all(B.evaluate(q, x, y) == 0 for q in eqs)]
        agree = p['models'] == brute
        totals['face_only_certified_false'] += p['face_only_certified_false']
        totals['face_only_certified_true'] += p['face_only_property'] is True
        totals['still_unresolved'] += not p['face_only_certified_false'] and p['face_only_property'] is not True
        totals['integer_models_complete'] += p['integer_models_complete']
        totals['brute_force_agree'] += agree
        ident = None
        if p['route'] == 'sturm_isolation':
            # independent algebraic identification: (x/a)^d = x^power with x != 0 gives x^(power-d) = a^-d
            r = p['interior_roots'][0]
            k = power-d
            if 'exact_root' in r:
                ident = Q(r['exact_root'])**k == Q(1, a**d)
            else:
                lo, hi = map(Q, r['isolating_interval'])
                ident = 0 < lo and lo**k < Q(1, a**d) < hi**k
        rows.append(dict(exponent=d, power=power, affine_coefficient=a, route=p['route'],
                         face_only_certified_false=p['face_only_certified_false'],
                         witness=p['face_only_certificate'], models=p['models'], brute_force_agree=agree,
                         algebraic_identification_x_pow_k_eq_a_pow_minus_d=ident))
        packets.append(p)
    return totals, rows, packets


def main():
    totals, rows, packets = affine_faces()
    assert totals['originally_unresolved'] == 36 and totals['face_only_certified_false'] == 36
    h1 = dump('affine_faces_refined.json', dict(schema='pp-affine-face-refined-corpus/1', box=list(map(str, BOX)),
                                                 totals=totals, cases=rows, packets=packets,
                                                 scope='face-only property decided for every originally unresolved case; '
                                                       'integer models completed by Sturm isolation or exact graph identity; not Lean checked'))
    packet = L.legendre_packet()
    fam = CurveFamily({'coefficients': [[0], [0, 1], [-1, -1], [1]]})
    transport, _ = L.certified_transport(fam, ['1/2', ['0', '1/2'], ['-1/2', '0'], ['0', '-1/2'], '1/2'])
    packet['family_bridge'] = transport
    m = packet['monodromy']
    assert m['N0'] == [[1, 2], [0, 1]] and m['N1'] == [[1, 0], [-2, 1]] and m['frobenius_agree']
    assert m['Ninf_outer'] == m['relations']['N1*N0']
    h2 = dump('legendre_certified_connection.json', packet)
    summary = dict(schema='pp-curve-certified-continuation-summary/1',
                   affine_faces=totals,
                   legendre=dict(N0=m['N0'], N1=m['N1'], Ninf_outer=m['Ninf_outer'],
                                 relation='N_outer = N1 N0 (gamma_0 then gamma_1)', frobenius_agree=m['frobenius_agree'],
                                 gamma2=m['gamma2'], log_coefficient_infinity=packet['positive_resonance']['log_coefficient'],
                                 period_determinant='8 pi i' if packet['period_determinant_closed_form']['consistent'] else None,
                                 taylor_steps={k: v['steps'] for k, v in packet['taylor_loops'].items()},
                                 cycle_matrix_max_radius={k: v['cycle_matrix_max_radius'] for k, v in packet['taylor_loops'].items()}),
                   receipts={'affine_faces_refined.json': h1, 'legendre_certified_connection.json': h2},
                   kernel_checked=False)
    dump('certified_continuation_summary.json', summary)
    print(json.dumps(summary, ensure_ascii=False))


if __name__ == '__main__':
    main()
