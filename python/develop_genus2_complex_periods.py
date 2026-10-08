"""Certified period matrices of genus-two curves with complex branch points: receipt writer."""
from pathlib import Path
import json
import sympy as sp
from flint import arb, acb
from perfectpower import genus2_certified_periods as g
from perfectpower import genus2_complex_periods as c

ROOT = Path(__file__).resolve().parents[1]
S = str
X = sp.symbols('x')


def coeffs(expr):
    return [int(v) for v in sp.Poly(sp.expand(expr), X).all_coeffs()[::-1]]


def mat(Om):
    return [[S(Om[i, k]) for k in range(2)] for i in range(2)]


def packet(pm):
    return {'ordered_branch_points': [S(z) for z in pm['roots']],
            'arc_simple_checks': len(pm['arc_checks']), 'arc_certified_simple': all(x[3] for x in pm['arc_checks']),
            'segment_signs_Y_plus_over_y_j': pm['signs'],
            'symplectic_basis_rows_a1_a2_b1_b2_on_gamma1_to_gamma4': pm['basis'],
            'cycle_periods_form0': [S(x) for x in pm['cycle_periods'][0]],
            'cycle_periods_form1': [S(x) for x in pm['cycle_periods'][1]],
            'relation_gamma1_gamma3_gamma5_contains_0': all(x.contains(0) for x in pm['relation_135']),
            'Omega': mat(pm['Omega']),
            'Riemann': {'symmetry_defect': S(pm['symmetry_defect']), 'Im_trace': S(pm['Im_trace']), 'Im_det': S(pm['Im_det']),
                        'certified': c.riemann_certified(pm)},
            'max_Omega_radius': S(max(pm['Omega'][i, k].rad() for i in range(2) for k in range(2)))}


def relation(pm1, pm2):
    M, rad, symp = c.integral_relation(pm1['Pi'], pm2['Pi'])
    return {'M': M, 'max_entry_radius': S(rad), 'M_t_J_M_equals_J': symp,
            'Omega_transformed_matches': c.matrices_close(c.omega_of(c.apply_matrix(pm1['Pi'], M)), pm2['Omega'])}


def real_reproduction(u):
    f = coeffs((X**2 - u[0])*(X**2 - u[1])*(X**2 - u[2]))
    pm = c.periods_of_polynomial(f)
    old = g.genus2_cycle_periods(list(u))
    diffs = [pm['cycle_periods'][p][j] - old[p][j] for p in (0, 1) for j in range(5)]
    pmb = c.periods_of_polynomial(f, basis=[list(v[:4]) for v in g.BASIS.values()])
    ref = g.period_matrix(list(u))['Omega']
    return {'sextic': 'y^2=(x^2-%d)(x^2-%d)(x^2-%d)' % u,
            'cycle_periods_all_contain_existing': all(d.contains(0) for d in diffs),
            'cycle_period_max_difference_bound': S(max(d.abs_upper() for d in diffs)),
            'Omega_existing_basis_matches_existing_receipt_module': c.matrices_close(pmb['Omega'], ref),
            'auto_basis_vs_existing_basis': relation(pmb, pm), 'packet': packet(pm)}


def symmetric_curve(name, f, mobius, D, D_text, order, closed_form):
    pm = c.periods_of_polynomial(f, mobius=mobius)
    M, rad, symp = c.automorphism_action(pm, D)
    sols, siegel = c.siegel_fixed_points(M)
    W = siegel[0]
    inside = all(_contains_exact(pm['Omega'][i, k], W[[0, 1, 1, 2][2*i + k]]) for i in range(2) for k in range(2))
    return {'curve': name, 'model': 'sextic via x=(%d t+%d)/(%d t+%d)' % mobius if mobius else 'sextic', 'packet': packet(pm),
            'automorphism': D_text, 'action_M': M, 'action_max_entry_radius': S(rad), 'M_symplectic': symp,
            'charpoly_M_const_first': c.int_charpoly(M), 'M_order': order, 'M_power_order_is_identity': c.int_matpow(M, order) == [[int(i == k) for k in range(4)] for i in range(4)],
            'exact_fixed_points_of_M': len(sols), 'fixed_points_in_Siegel_space': [S(w) for w in W],
            'closed_form': closed_form, 'Omega_ball_contains_closed_form': inside,
            'unique_Siegel_fixed_point': len(siegel) == 1}


def _contains_exact(ball, w):
    """Certify that an acb ball contains the exact algebraic number w (via an Arb enclosure of w)."""
    re, im = sp.re(w), sp.im(w)
    def enc(v):
        v = sp.nsimplify(v)
        if v.is_Rational:
            return arb(int(v.p))/int(v.q)
        base = sp.N(v, 90)
        return arb(S(base)) + arb(0, 1e-80)
    return bool(ball.real.contains(enc(re)) and ball.imag.contains(enc(im)))


def main():
    out = {'precision_bits': 200, 'engine': 'Arb ball arithmetic via python-flint (acb.integral rigorous quadrature, fmpz_poly.complex_roots)'}
    C5 = c.model_intersection_matrix()
    out['model_intersection_matrix_gamma1_to_gamma5'] = C5
    out['model_is_chain_plus_one'] = C5 == g.chain_intersection(1)
    out['symplectic_basis_from_reduction'] = c.symplectic_basis([r[:4] for r in C5[:4]])
    out['a_real_branch_points'] = [real_reproduction(u) for u in [(1, 4, 9), (2, 3, 7)]]
    z6 = (acb(0, 1)*arb.pi()/3).exp(); z8 = (acb(0, 1)*arb.pi()/4).exp()
    out['b_automorphisms'] = [
        symmetric_curve('y^2=x^6-1', coeffs(X**6 - 1), None, [z6, z6**2], '(x,y)->(zeta6 x, y): dx/y->zeta6 dx/y, x dx/y->zeta6^2 x dx/y', 6,
                        'Omega=[[-1+i sqrt3/2, 1/2],[1/2, -1+i sqrt3/2]]'),
        symmetric_curve('y^2=x^5-x (Bolza)', [0, -1, 0, 0, 0, 1], (2, 1, 1, 0), [z8, z8**3], '(x,y)->(i x, zeta8 y): dx/y->zeta8 dx/y, x dx/y->zeta8^3 x dx/y', 8,
                        'Omega=[[1/2+i/sqrt2, -1/2],[-1/2, 1/2+i/sqrt2]]')]
    f_c = coeffs((X**2 - 2)*(X**2 + 1)*(X**2 + 2*X + 5))
    pm = c.periods_of_polynomial(f_c)
    pm_im = c.periods_of_polynomial(f_c, order='im_re')
    controls = []
    for j in range(5):
        bad = c.periods_of_polynomial(f_c, sign_flip=j)
        try:
            M, rad, symp = c.integral_relation(pm['Pi'], bad['Pi'])
            res = 'integral, symplectic=%s' % symp
        except ArithmeticError:
            res = 'no integral relation'
        controls.append({'flipped_segment': j + 1, 'Riemann_certified': c.riemann_certified(bad), 'relation_to_correct_periods': res,
                         'relation_gamma1_gamma3_gamma5_contains_0': all(x.contains(0) for x in bad['relation_135'])})
    out['c_two_conjugate_pairs_one_real_pair'] = {
        'curve': 'y^2=(x^2-2)(x^2+1)(x^2+2x+5)', 'coefficients_const_first': f_c, 'packet': packet(pm),
        'second_arc_order_Im_then_Re': packet(pm_im), 'arcs_related_by_Sp4Z': relation(pm, pm_im),
        'negative_control_wrong_sheet_on_one_segment': controls}
    mob = []
    for name, f, m0, m1 in [('y^2=(x^2-2)(x^2+1)(x^2+2x+5)', f_c, None, (1, 1, 1, -2)),
                            ('y^2=x^6-1', coeffs(X**6 - 1), None, (1, 2, 3, 4)),
                            ('y^2=x^5-x+1 (quintic: two conjugate pairs, one real root)', coeffs(X**5 - X + 1), (0, 1, 1, 0), (3, 1, 1, -1))]:
        p0 = c.periods_of_polynomial(f, mobius=m0); p1 = c.periods_of_polynomial(f, mobius=m1)
        mob.append({'curve': name, 'map_0': m0, 'map_1': m1, 'Omega_0': mat(p0['Omega']), 'Omega_1': mat(p1['Omega']),
                    'Riemann_0': c.riemann_certified(p0), 'Riemann_1': c.riemann_certified(p1),
                    'branch_points_1': [S(z) for z in p1['roots']], 'relation': relation(p0, p1)})
    out['d_moebius_consistency'] = mob
    out['scope'] = ('Arb-certified periods along straight-segment arcs through the branch points of rational sextics (quintics after a '
                    'rational Moebius map). The intersection matrix is computed exactly on the model configuration and transported by '
                    'the simple-arc homeomorphism; the arc simplicity, the branch signs and all periods are certified in Arb. '
                    'Closed forms for the two symmetric curves are certified containments plus an exact (sympy) uniqueness of the '
                    'Siegel fixed point of the certified action matrix. Not claimed: curves with non-rational coefficients, '
                    'configurations whose straight arc passes too close to a branch point for the available precision, any '
                    'statement beyond the listed curves, or a machine-checked proof of the topological transport lemma.')
    path = ROOT/'receipts/curve_structure/genus2_complex_periods.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(out, indent=1, sort_keys=True) + '\n')
    for r in out['a_real_branch_points']:
        print(r['sextic'], r['cycle_periods_all_contain_existing'], r['Omega_existing_basis_matches_existing_receipt_module'], r['auto_basis_vs_existing_basis']['M'])
    for r in out['b_automorphisms']:
        print(r['curve'], r['packet']['Riemann']['certified'], r['action_M'], r['charpoly_M_const_first'], r['Omega_ball_contains_closed_form'], r['unique_Siegel_fixed_point'])
    k = out['c_two_conjugate_pairs_one_real_pair']
    print(k['curve'], k['packet']['Riemann']['certified'], k['packet']['segment_signs_Y_plus_over_y_j'], k['arcs_related_by_Sp4Z']['M'], [(x['relation_to_correct_periods'], x['Riemann_certified'], x['relation_gamma1_gamma3_gamma5_contains_0']) for x in k['negative_control_wrong_sheet_on_one_segment']])
    for r in mob:
        print(r['curve'], r['Riemann_0'], r['Riemann_1'], r['relation']['M'], r['relation']['M_t_J_M_equals_J'], r['relation']['Omega_transformed_matches'])


if __name__ == '__main__':
    main()
