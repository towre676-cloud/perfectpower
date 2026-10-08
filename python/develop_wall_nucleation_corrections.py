"""One-loop CW, thermal-function, two-loop and thermal-vector corrections to the biased-vacuum nucleation."""
from pathlib import Path
from math import sqrt, pi, log, log10
import hashlib, json
import numpy as np
from perfectpower.dimensionful_walls import WallModel, radiation_H
from perfectpower import wall_nucleation as wn
from perfectpower import wall_nucleation_corrections as wc

ROOT = Path(__file__).resolve().parents[1]
TEMPERATURES = (0.03, 1., 25., 50., 100., 150., 300., 1000., 2000., 2999.)
# Relative thermal TE vector free energy per area (2 W + 1 Z, g=0.65, g'=0.36), Richardson values from
# receipts/flavor_cosmology/wall_pair_decay.json at commit 0546f5842deb2e3242b4bbc1ea0661a965b7d179
# (file sha256 71b8a6584f13e991ee71b0cf01114164fc8c2900dc3726b618f4b22dbb6daf1d), retuned radial candidate wall.
VECTOR_FREE_ENERGY_GEV3 = {25.: 7.6522468941869475, 50.: 132.12875418941675,
                           100.: 1083.3035407221805, 150.: 3098.610561564327}
VECTOR_SOURCE = {'commit': '0546f5842deb2e3242b4bbc1ea0661a965b7d179',
                 'file': 'receipts/flavor_cosmology/wall_pair_decay.json',
                 'sha256': '71b8a6584f13e991ee71b0cf01114164fc8c2900dc3726b618f4b22dbb6daf1d',
                 'key': 'thermal_spacing_extrapolation[].O_spacing_squared_Richardson_GeV3'}
BETA_OVER_LAM = 18/(16*pi*pi)   # beta_lam/lam^2 for lam phi^4/4 of one real scalar


def gstar(T):
    return 107.75 if T > .2 else 10.75


def slope(pot, eps, d, s0):
    h = 2e-5
    return (wc.bounce(pot, eps - h, d)['s'] - s0)/(-h)


def tension(pot):
    """Reduced kink tension int sqrt(2(U-U_vac)) between the eps=0 vacua of pot."""
    from scipy.integrate import quad
    f, b, t = wc.stationary_points(pot, 1e-12)
    Uv = float(pot.U(t, 0.))
    return quad(lambda x: sqrt(max(2*(float(pot.U(x, 0.)) - Uv), 0.)), f, t, limit=400, epsabs=1e-14)[0]


def main():
    source = ROOT/'receipts/flavor_cosmology/dimensionful_walls.json'
    old = json.loads(source.read_text())
    model = WallModel(**old['declared_model_inputs'])
    v, lam, c = model.v_GeV, model.lam, model.thermal_c
    M, g = model.heavy_mass_GeV, model.current_g_GeV
    nuc = ROOT/'receipts/flavor_cosmology/wall_nucleation.json'
    out = {'input_dimensionful_receipt_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
           'input_nucleation_receipt_sha256': hashlib.sha256(nuc.read_bytes()).hexdigest(),
           'declared_model': model.__dict__, 'vector_free_energy_source': VECTOR_SOURCE,
           'scheme': ('On-shell (zero-momentum) renormalisation: V_CW=(1/64 pi^2)[m^4(log(m^2/m_v^2)-3/2)+2 m^2 m_v^2] '
                      'for phi (and the heavy mediator), so that at T=0 the vev v and curvature mass m_v^2=2 lam v^2 '
                      'are the tree values. Re-part (log|m^2|) where m^2(phi)<0.')}

    # Zero-temperature potential checks and tension shifts.
    A0, A2 = M*M/(lam*v*v), 4*g*g/(lam*M*M)
    tree0 = wc.Corrected(lam, parts=())
    cw0 = wc.Corrected(lam, parts=('cw', 'heavy'), heavy=(A0, A2))
    ms0 = wc.Corrected(lam, parts=('cw_msbar',))
    sp_tree, sp_cw, sp_ms = (wc.corrected_spinodal(p) for p in (tree0, cw0, ms0))
    sig_tree, sig_cw = tension(tree0), tension(cw0)
    h = 1e-6
    out['zero_temperature'] = {
        'OS_conditions_dV_at_v': float(cw0.ddelta(np.array([1.]))[0]),
        'OS_conditions_d2V_at_v': float((cw0.ddelta(np.array([1 + h])) - cw0.ddelta(np.array([1 - h])))[0]/(2*h)),
        'heavy_mediator_reduced_coefficients_A0_A2': [A0, A2],
        'heavy_mediator_max_abs_field_dependence_on_[-1.2,1.2]': (lambda hv: float(np.max(abs(
            hv.delta(np.linspace(-1.2, 1.2, 241)) - hv.delta(np.array([1.]))[0]))))(
            wc.Corrected(lam, parts=('heavy',), heavy=(A0, A2))),
        'Higgs_loop_bound_reduced': 4/(64*pi*pi)*(2*2*0.13*246.**2*1e-7*v*v + (1e-7*v*v)**2)*10/(lam*v**4),
        'spinodal_tree': sp_tree, 'spinodal_OS': sp_cw, 'spinodal_MSbar_mu_mv': sp_ms,
        'spinodal_relative_shift_OS': sp_cw['eps_sp']/sp_tree['eps_sp'] - 1,
        'kink_tension_reduced_tree': sig_tree, 'kink_tension_reduced_OS': sig_cw,
        'kink_tension_relative_shift_OS': sig_cw/sig_tree - 1,
        'note': ('The near-spinodal cubic law of the corrected potential is listed for completeness only: the one-loop '
                 'curvature has an IR log at m^2(phi)=0, next to the spinodal, so its asymptotic constants are not '
                 'controlled. Bounces at the critical biases stay at Delta>=0.003 where the false-vacuum m^2 is O(0.1-0.2) lam v^2.')}

    rows = []
    for T in TEMPERATURES:
        vT = v*sqrt(1 - c*T*T/(lam*v*v)); r, tau = v/vT, T/vT
        ymin, ymax = -lam*r*r/tau**2, lam*(3*1.6**2 - r*r)/tau**2
        J_ok = ymin >= -4*pi*pi
        spline = wc.ThermalSpline(ymin, ymax, with_J=J_ok)
        mk = lambda parts, **kw: wc.Corrected(lam, r=r, tau=tau, parts=parts, heavy=(A0, A2), spline=spline, **kw)
        if J_ok:
            central_parts = ('cw', 'heavy', 'thermal1')
            alt = mk(central_parts, y_shift=lam/4)
            alt_label = 'daisy-shifted Re J_B(m^2/T^2+lam/4)'
        else:
            central_parts = ('cw', 'heavy', 'thermal1_removal')
            alt = mk(('cw', 'heavy'))
            alt_label = 'declared high-T phi self-loop mass kept'
        pot, cw_only = mk(central_parts), mk(('cw', 'heavy'))
        sp = wc.corrected_spinodal(pot)
        H = radiation_H(T, gstar(T))
        row = {'T_GeV': T, 'v_T_GeV': vT, 'H_GeV': H, 'thermal_JB_valid': J_ok,
               'central_parts': list(central_parts), 'alternative_thermal': alt_label,
               'corrected_spinodal_eps': sp['eps_sp'], 'eps_declared': model.h(T)/(lam*vT**3)}
        for d, scale, Hu in ((3, vT/(sqrt(lam)*T), H/T), (4, 1/lam, H/vT)):
            s_star, S_star = wn.nucleation_threshold(d, scale, Hu)
            e_tree, how = wn.critical_eps(s_star, d)
            res = {'S_star': S_star, 's_star': s_star, 'eps_star_tree': e_tree, 'tree_method': how,
                   'eps_star_tree_over_sp': e_tree/wn.EPS_SPINODAL}
            # Corrected action at the tree critical bias.
            if how == 'bounce' and e_tree < sp['eps_sp'] - 1e-6:
                bt = wc.bounce(pot, e_tree, d)
                res['S_corrected_at_tree_eps'] = scale*bt['s']
                res['S_corrected_at_tree_eps_over_S_star'] = bt['s']/s_star
                res['virial_defect_corrected_at_tree_eps'] = bt['virial_defect']
            elif how == 'bounce':
                res['S_corrected_at_tree_eps'] = 0.
                res['S_corrected_at_tree_eps_note'] = 'tree critical bias lies above the corrected spinodal: no barrier'
            # Corrected critical bias.
            try:
                e_c = wc.critical_eps(pot, s_star, d, hi=sp['eps_sp'] - 2e-4)
                method = 'bounce'
            except ValueError:
                e_c = sp['eps_sp'] - (s_star/sp['C'][d])**(4/(6 - d))
                method = 'near_spinodal_asymptotic_uncontrolled'
            res.update({'eps_star_corrected': e_c, 'corrected_method': method,
                        'eps_star_corrected_over_tree_sp': e_c/wn.EPS_SPINODAL,
                        'eps_star_relative_shift': e_c/e_tree - 1})
            if method == 'bounce':
                b = wc.bounce(pot, e_c, d)
                ds = slope(pot, e_c, d, b['s'])
                f1 = lambda dv: wc.first_order_shift(b, dv, d)
                # bracket pieces (reduced action units)
                cw_shift = abs(b['s'] - wc.bounce(wc.Corrected(lam, r=r, tau=tau, parts=()), e_c, d)['s']) \
                    if e_c < wn.EPS_SPINODAL - 1e-6 else abs(b['s'])
                MIR = 1/b['radius_core']**2
                ir = mk(('cw', 'heavy') + central_parts[2:], M_IR=MIR)
                fig8 = lambda x: wc.two_loop_thermal(x, lam, tau, spline)[0]
                suns = lambda x: wc.two_loop_thermal(x, lam, tau, spline)[1]
                pieces = {
                    'two_loop_zero_T_beta_estimate': BETA_OVER_LAM*lam*cw_shift,
                    'CW_IR_sensitivity_M_IR=1/R_core^2': f1(lambda x: ir.delta(x) - pot.delta(x))[1],
                    'thermal_one_loop_alternative': f1(lambda x: alt.delta(x) - pot.delta(x))[1],
                    'two_loop_thermal_figure_eight': f1(fig8)[1],
                    'two_loop_thermal_sunset_estimate': f1(suns)[1]}
                width = sum(pieces.values())
                vec = 0.
                if d == 3 and T in VECTOR_FREE_ENERGY_GEV3:
                    R = b['radius_core']/(sqrt(lam)*vT)
                    vec = VECTOR_FREE_ENERGY_GEV3[T]*4*pi*R*R/T
                    res['vector_tension_shift_S3_over_T'] = vec
                    res['bubble_radius_GeV_inv'] = R
                res.update({'corrected_bounce_s': b['s'], 'virial_defect': b['virial_defect'],
                            'ds_deps': ds, 'bracket_pieces_reduced_action': pieces,
                            'bracket_half_width_reduced_action': width,
                            'S_bracket_half_width': scale*width,
                            'eps_star_corrected_bracket': [e_c - width/abs(ds), e_c + (width + vec/scale)/abs(ds)],
                            'dominant_bracket_piece': max(pieces, key=pieces.get)})
                res['first_order_CW_shift_check'] = f1(lambda x: cw_only.delta(x))[0]
            row['d%d' % d] = res
        e3, e4 = row['d3']['eps_star_corrected'], row['d4']['eps_star_corrected']
        row['easier_channel_corrected'] = 'thermal_O3' if e3 < e4 else 'quantum_O4'
        row['easier_channel_tree'] = 'thermal_O3' if row['d3']['eps_star_tree'] < row['d4']['eps_star_tree'] else 'quantum_O4'
        row['eps_eff_tree'] = min(row['d3']['eps_star_tree'], row['d4']['eps_star_tree'])
        row['eps_eff_corrected'] = min(e3, e4)
        lo = [row['d%d' % d].get('eps_star_corrected_bracket', [row['d%d' % d]['eps_star_corrected']]*2) for d in (3, 4)]
        row['eps_eff_corrected_bracket'] = [min(lo[0][0], lo[1][0]), min(lo[0][1], lo[1][1])]
        row['bias_amplification_needed_tree'] = row['eps_eff_tree']/row['eps_declared'] if row['eps_declared'] > 0 else None
        row['bias_amplification_needed_corrected'] = row['eps_eff_corrected']/row['eps_declared'] if row['eps_declared'] > 0 else None
        rows.append(row)
        print(T, row['easier_channel_tree'], row['easier_channel_corrected'], row['eps_eff_tree'], row['eps_eff_corrected'],
              row['eps_eff_corrected_bracket'], flush=True)
    out['rows'] = rows

    # Nucleation temperature for amplified-bias benchmarks: eps_A(T)=q eps_sp (1-(T/T_on)^2)(v/v_T)^3.
    Ts = np.array([r['T_GeV'] for r in rows])
    def T_n(q, key, idx=None):
        vals = np.array([r[key] if idx is None else r[key][idx] for r in rows])
        epsA = np.array([q*wn.EPS_SPINODAL*max(0., 1 - (T/model.bias_onset_GeV)**2)*(v/r['v_T_GeV'])**3
                         for T, r in zip(Ts, rows)])
        gap = epsA - vals
        if gap[0] < 0:
            return None
        k = np.flatnonzero(gap < 0)
        if not k.size:
            return float(Ts[-1])
        k = k[0]
        return float(Ts[k - 1] + (Ts[k] - Ts[k - 1])*gap[k - 1]/(gap[k - 1] - gap[k]))
    bench = []
    for q in (0.99, 0.995, 1.0):
        bench.append({'q_eps_at_T0_over_eps_sp': q, 'amplification_over_declared': q*wn.EPS_SPINODAL/rows[0]['eps_declared'],
                      'T_n_tree_GeV': T_n(q, 'eps_eff_tree'), 'T_n_corrected_GeV': T_n(q, 'eps_eff_corrected'),
                      'T_n_corrected_bracket_GeV': [T_n(q, 'eps_eff_corrected_bracket', 1), T_n(q, 'eps_eff_corrected_bracket', 0)]})
    out['nucleation_temperature_benchmarks'] = {
        'definition': 'Highest T on the grid-interpolated (linear in T) curve where the amplified bias reaches the easier critical bias; bias shape (1-(T/3000 GeV)^2) as declared.',
        'rows': bench}

    # Declared bias: thin-wall action and tension shifts.
    sigma_phys = lambda vT: sig_tree*sqrt(lam)*vT**3
    decl = []
    for r in rows:
        if r['eps_declared'] <= 0:
            continue
        T, vT = r['T_GeV'], r['v_T_GeV']
        s3 = 16*pi*sig_tree**3/(3*(2*r['eps_declared'])**2)
        S3T = vT/(sqrt(lam)*T)*s3
        dv = VECTOR_FREE_ENERGY_GEV3.get(T, 0.)/sigma_phys(vT)
        decl.append({'T_GeV': T, 'log10_S3_over_T_tree_thin_wall': log10(S3T),
                     'log10_shift_from_CW_tension': 3*log10(sig_cw/sig_tree),
                     'vector_relative_tension_shift': dv, 'log10_shift_from_vector': 3*log10(1 + dv)})
    out['declared_bias_thin_wall'] = {'rows': decl, 'conclusion': 'S3/T is of order 10^50 or more at every grid temperature with the declared bias; no correction changes its logarithm by more than 10^-3. No nucleation temperature exists for the declared bias.'}

    shifts = [(r['T_GeV'], d, r['d%d' % d]['eps_star_relative_shift']) for r in rows for d in (3, 4)
              if r['d%d' % d]['corrected_method'] == 'bounce']
    out['conclusions'] = {
        'dominant_correction': 'zero-temperature one-loop Coleman-Weinberg (on-shell)',
        'spinodal_relative_shift_OS': out['zero_temperature']['spinodal_relative_shift_OS'],
        'eps_star_relative_shifts_bounce_rows': shifts,
        'declared_bias_nucleates': False,
        'nucleation_temperature_declared_bias': None}
    out['scope'] = ('Supplied spectator model; single-field reduced bounces (the three-field sandwich of wall_nucleation '
                    'is not recomputed for the corrected potential); fluctuation determinant still the declared exp(+-20) band, '
                    'not included in the brackets above. Two-loop terms are estimates, not computed diagrams with counterterms. '
                    'The thermal vector free energy belongs to the retuned radial candidate wall (another quartic) and is '
                    'transported as an order-of-magnitude positive tension shift. Floating-point bounces, no interval enclosure.')
    path = ROOT/'receipts/flavor_cosmology/wall_nucleation_corrections.json'
    path.write_text(json.dumps(out, indent=1, sort_keys=True, default=float) + '\n')
    print(json.dumps(out['nucleation_temperature_benchmarks'], indent=1))
    print(json.dumps(out['conclusions'], indent=1, default=float))


if __name__ == '__main__':
    main()
