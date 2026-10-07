"""Certified period packet, integral cycle map and node monodromy for split genus-two curves."""
from pathlib import Path
import json
from flint import arb, acb
from perfectpower import genus2_certified_periods as g

ROOT = Path(__file__).resolve().parents[1]
CURVES = [(1, 4, 9), (2, 3, 7)]
S = str


def contains_zero(x):
    return bool(x.contains(0))


def curve_packet(u):
    pm = g.period_matrix(list(u))
    oq = g.omega_from_quotients(list(u))
    roots = g.genus2_roots(list(u))
    radii = []
    for j in range(5):
        a, b = roots[j], roots[j + 1]
        gaps = [abs(roots[k] - (a + b)/2) for k in range(6) if k not in (j, j + 1)]
        h = (b - a)/2
        radii.append(float(((h + min(gaps))/2).mid()))
    contour = []
    for j in range(5):
        for p in (0, 1):
            d = g.segment_integral(roots, j, p) - g.loop_integral(roots, j, p, radii[j])
            contour.append({'cycle': j + 1, 'form': 'z^%d dz/y' % p, 'difference_upper_bound': S(d.abs_upper())})
    Om, Oq = pm['Omega'], oq['Omega']
    diffs = [Om[i, j] - Oq[i, j] for i in range(2) for j in range(2)]
    signs = {('%+d,%+d,%+d' % (s, e1, e2)): g.polarization_identity(oq['cycle_map']['maps'], s, e1, e2)
             for s in (1, -1) for e1 in (1, -1) for e2 in (1, -1)}
    W = oq['cycle_map']['E1_lattice']
    agm = g.agm_periods(*u)
    return {
        'u_roots': list(u), 'sextic': 'y^2=(z^2-%d)(z^2-%d)(z^2-%d)' % u,
        'cycle_periods_eta0': [S(x) for x in pm['cycle_periods'][0]],
        'cycle_periods_eta1': [S(x) for x in pm['cycle_periods'][1]],
        'Omega': [[S(Om[i, j]) for j in range(2)] for i in range(2)],
        'Riemann': {'symmetry_defect_contains_0': contains_zero(pm['symmetry_defect']),
                    'symmetry_defect': S(pm['symmetry_defect']),
                    'Im_trace': S(pm['Im_trace']), 'Im_det': S(pm['Im_det']),
                    'Im_Omega_positive_definite': bool(pm['Im_trace'] > 0 and pm['Im_det'] > 0)},
        'integral_cycle_map': oq['cycle_map']['maps'],
        'polarization_identity_defect_by_signs': signs,
        'tau_E1': S(oq['tau_E1']), 'tau_E2': S(oq['tau_E2']),
        'tau_orientations_positive': bool(oq['tau_E1'].imag > 0 and oq['tau_E2'].imag > 0),
        'Omega_from_quotients_equal': all(contains_zero(x) for x in diffs),
        'Omega_from_quotients_max_radius': max(S(x.abs_upper()) for x in diffs),
        'Omega11_minus_2_Omega12': S(Om[0, 0] - 2*Om[0, 1]),
        'E1_AGM': {'segment_r1_r2': S(abs(W[0])/2), 'agm_r1_r2': S(agm[0]),
                   'segment_r2_r3': S(abs(W[1])/2), 'agm_r2_r3': S(agm[1]),
                   'equal': bool(contains_zero(abs(W[0])/2 - agm[0]) and contains_zero(abs(W[1])/2 - agm[1]))},
        'contour_deformation': contour}


def main():
    out = {'precision_bits': 200, 'engine': 'Arb ball arithmetic via python-flint (acb.integral rigorous quadrature)'}
    out['curves'] = [curve_packet(u) for u in CURVES]
    node = []
    for p in (0, 1):
        for r in g.picard_lefschetz([1e-2, 1e-3, 1e-4, 1e-5, 1e-6, 1e-7, 1e-8], f_power=p):
            node.append({'form': 'z^%d dz/y' % p, 'delta': r['delta'], 'P_vanishing': S(r['P_vanishing']),
                         'mirror_relation': 'equal' if contains_zero(r['P_mirror_vanishing'] - r['P_vanishing']) else
                                            ('opposite' if contains_zero(r['P_mirror_vanishing'] + r['P_vanishing']) else 'neither'),
                         'regularised_b1': S(r['regularised_b1']),
                         'regularised_T_v_squared': S(r['regularised']), 'half_coefficient_value': S(r['half_coefficient']),
                         'b1_period': S(r['b1_period']),
                         'fitted_coefficient_over_P5_2pii': S(r['fitted_coefficient_over_P5_2pii']) if 'fitted_coefficient_over_P5_2pii' in r else None})
    out['node_family'] = {'family': 'Q=(u-1)(u-4)(u-4-delta)', 'rows': node,
                          'statement': 'P4+(P5/(pi i)) log delta converges with O(delta) steps (monodromy T_v^2: a full turn of a branch point is a squared half-twist, and Birman-Hilden lifts each half-twist to T_v); the coefficient P5/(2 pi i) instead drifts linearly in log delta. The mirror vanishing periods are equal for dz/y and opposite for z dz/y (z->-z parity), and they twist b1 with opposite intersection signs, so b1+((P5-P1)/(pi i)) log delta converges; for dz/y the b1 period itself has no logarithm.'}
    out['scope'] = ('Two explicit (2,2)-split curves with six real branch points and one degenerating family. All numbers are Arb balls '
                    'with proven radii, except the convergence statement near the node, which compares certified values at '
                    'finitely many delta (an asymptotic regularity check, not a proof of the full expansion).')
    path = ROOT/'receipts/curve_structure/genus2_certified_periods.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=1, sort_keys=True)+'\n')
    for c in out['curves']:
        print(c['sextic'], c['Riemann']['Im_Omega_positive_definite'], c['Riemann']['symmetry_defect_contains_0'],
              c['Omega_from_quotients_equal'], c['tau_orientations_positive'], c['E1_AGM']['equal'], c['integral_cycle_map'],
              c['polarization_identity_defect_by_signs'], c['Omega11_minus_2_Omega12'], max(float(x['difference_upper_bound'].split()[0].strip('[')) for x in c['contour_deformation']))
    for r in node[::3]:
        print(r['form'], r['delta'], r['regularised_T_v_squared'][:60], r['mirror_relation'], r['regularised_b1'][:50], r['fitted_coefficient_over_P5_2pii'] and r['fitted_coefficient_over_P5_2pii'][:40])


if __name__ == '__main__':
    main()
