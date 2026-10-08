"""Computed two-loop thermal potential: validation, S3/T and amplified-bias nucleation temperatures.

Replaces the two-loop estimates of develop_wall_nucleation_corrections by the computed figure-eight and
sunset (T=0 and thermal parts, MS-bar, converted to the on-shell scheme, Parwani-type resummation).
Writes receipts/flavor_cosmology/wall_two_loop_thermal_validation.json and wall_two_loop_thermal.json.
"""
from pathlib import Path
from math import sqrt, pi, log
import hashlib, json, time
import numpy as np
from perfectpower.dimensionful_walls import WallModel, radiation_H
from perfectpower import wall_nucleation as wn
from perfectpower import wall_nucleation_corrections as wc
from perfectpower import wall_two_loop_thermal as w2

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'receipts/flavor_cosmology'
TEMPERATURES = (0.03, 1., 25., 50., 100., 150., 300., 1000., 2000., 2999.)
THERMAL_FROM = 2000.        # as in wall_nucleation_corrections: Re J_B central only where |m^2|/T^2<4 pi^2
MU_FACTORS = (0.5, 2**-0.5, 1., 2**0.5, 2.)
IR_FACTORS = (0.25, 4.)


def gstar(T):
    return 107.75 if T > .2 else 10.75


def rnd(x, k=12):
    """Deterministic rounding of floats for the receipts."""
    if isinstance(x, dict):
        return {a: rnd(b, k) for a, b in x.items()}
    if isinstance(x, (list, tuple)):
        return [rnd(b, k) for b in x]
    if isinstance(x, (float, np.floating)):
        return float(f'{float(x):.{k}g}')
    if isinstance(x, np.integer):
        return int(x)
    return x


# ---------------------------------------------------------------- validation
def validation():
    out = {}
    b, f = w2.matsubara_sunset_check(1.3, 0.7, 1.1)
    out['matsubara_decomposition'] = {'E': [1.3, 0.7, 1.1], 'T': 1., 'brute_force_sum_N3000': b, 'formula': f,
                                      'relative_difference': abs(b/f - 1)}
    out['contour_vs_log_sin_ReJB'] = [{'y': y, 'contour': w2.J_B(y).real, 'wall_nucleation_corrections.re_JB': wc.re_JB(y)}
                                      for y in (-30., -5., -0.5, 0.5, 4., 30.)]
    out['contour_vs_highT_series_JB'] = [{'y': y, 'contour': [w2.J_B(y).real, w2.J_B(y).imag],
                                          'series': [w2.J_B_highT(y).real, w2.J_B_highT(y).imag]}
                                         for y in (-20., -2., -0.1, 0.1, 2., 20.)]
    out['tadpole_vs_wall_nucleation_corrections'] = [{'y': y, 'i_T': w2.i_T(y).real,
                                                      'tadpole_i/2pi^2': wc.tadpole_i(y)/(2*pi*pi)} for y in (0.5, 4., 30.)]
    out['figure_eight_massless'] = {'i_T(0)': w2.i_T(0.).real, 'expected': 1/12,
                                    'note': '(lam_s/8) I_T(0)^2 = lam_s T^4/1152, the two-loop lam phi^4 free energy'}
    out['sunset_angular_check'] = [{'y': y, 'log_formula': [w2.h_2(y).real, w2.h_2(y).imag],
                                    'numerical_angle': [w2.h_2_direct(y).real, w2.h_2_direct(y).imag]}
                                   for y in (-15., -2., 0.3, 2.)]
    small = []
    for y in (1e-2, 1e-3, 1e-4, 1e-5, 1e-6):
        h = w2.h_2(y).real
        small.append({'y': y, 'h2+log(m/T)/32pi^2': h + 0.25*log(y)*w2.KAPPA})
    out['sunset_small_m_limit'] = {
        'prediction': w2.H2_SMALL_M_CONST,
        'derivation': ('H_T -> T^2 kappa[1/(4eps)+1/2+log(mu/3m)] (3d sunset of the zero modes; the one- and '
                       'no-zero-mode parts cancel at m=0 because the massless 4d sunset vanishes), minus the '
                       'I_T(d) subdivergence pole and minus 3 I_T B_on; uses I_T(d)=T^2/12[1+eps(2log(mu/4piT)+2+2zeta\'(-1)/zeta(-1))].'),
        'values': small}
    out['parwani_linear_term'] = {
        'resummed_Im_F_over_s': [{'s': s, 'value': w2.parwani_linear_coefficient(s, 0.6)} for s in (1e-2, 1e-3)],
        'unresummed_Im_F_over_s': [{'s': s, 'value': w2.parwani_linear_coefficient(s, 0.6, resummed=False)} for s in (1e-2, 1e-3)],
        'unresummed_expected': -0.6/(192*pi),
        'note': 'lam_s=0.6: the M T^3 term of the figure-eight is cancelled by -Pi I_T/2 (each daisy counted once).'}
    # scheme checks on the declared model
    lam, v = 0.1, 30000.
    MV = sqrt(2*lam)*v
    phi = np.linspace(-1.6, 1.6, 33)*v
    rows = []
    for T in (0., 2000., 2999.):
        tab = None if T == 0 else w2.ThermalTables(-lam*v*v/T**2*1.02, lam*(3*(1.8*v)**2 - v*v)/T**2)
        pots = [w2.TwoLoopPotential(lam, v, T, tables=tab, mu=MV*f) for f in MU_FACTORS]
        os_ = [p.os_loops(phi) for p in pots]
        os_ = [a - a[16] for a in os_]
        ms = [p.msbar_loops(phi) - p.os_loops(phi) for p in pots]
        ms = [a - a[16] for a in ms]
        one = [p.one_loop_msbar_minus_os(phi) for p in pots]
        one = [a - a[16] for a in one]
        d2 = pots[2].delta(phi)
        rows.append({'T_GeV': T,
                     'OS_two_loop_max_mu_dependence_GeV4': max(float(np.max(np.abs(a - os_[2]))) for a in os_),
                     'two_loop_size_GeV4': float(np.max(np.abs(d2 - d2[16]))),
                     'MSbar_two_loop_one_loop_matched_mu_spread_GeV4': float(np.max(np.ptp(np.array(ms), axis=0))),
                     'MSbar_one_loop_tree_matched_mu_spread_GeV4': float(np.max(np.ptp(np.array(one), axis=0))),
                     'mu_over_m_v': list(MU_FACTORS)})
        if T == 0:
            p = pots[2]; h = 1.
            fd = lambda ph: float(p.delta(np.array([ph]))[0])
            rows[-1]['OS_conditions_two_loop'] = {'dV_dphi_at_v_GeV3': (fd(v + h) - fd(v - h))/(2*h),
                                                  'd2V_dphi2_at_v_GeV2': (fd(v + h) - 2*fd(v) + fd(v - h))/h**2,
                                                  'a2_GeV2': p.a2, 'a4': p.a4}
    out['scheme'] = rows
    out['constants'] = {'C_sun': w2.C_SUN, 'B_on_const': w2.B_ON_CONST, 'kappa': w2.KAPPA}
    return out


# ---------------------------------------------------------------- physics
def first_order(b, D, d):
    return wc.first_order_shift(b, D, d)[0]


def slope(pot, eps, d, s0):
    h = 2e-5
    return (wc.bounce(pot, eps - h, d)['s'] - s0)/(-h)


def main():
    t0 = time.time()
    val = validation()
    (OUT/'wall_two_loop_thermal_validation.json').write_text(json.dumps(rnd(val), indent=1, sort_keys=True) + '\n')
    print('validation done', time.time() - t0, flush=True)

    source = OUT/'dimensionful_walls.json'
    old_path = OUT/'wall_nucleation_corrections.json'
    old = json.loads(old_path.read_text())
    model = WallModel(**json.loads(source.read_text())['declared_model_inputs'])
    v, lam, c = model.v_GeV, model.lam, model.thermal_c
    M, g = model.heavy_mass_GeV, model.current_g_GeV
    A0, A2 = M*M/(lam*v*v), 4*g*g/(lam*M*M)
    MV = sqrt(2*lam)*v
    out = {'input_dimensionful_receipt_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
           'input_one_loop_receipt_sha256': hashlib.sha256(old_path.read_bytes()).hexdigest(),
           'declared_model': model.__dict__,
           'scheme': ('On-shell (zero-momentum) at two loops: V_tree(lam,v)+V_CW^OS+V_1T+(1/2)[kappa A+I_T] delta x'
                      '+V_2+a2 phi^2+a4 phi^4 with V\'(v)=0, V\'\'(v)=2 lam v^2 at T=0; Parwani-type resummation of the '
                      'thermal parts with Pi=(lam_s/2) Re I_T; Re of the x+i0 continuation (Weinberg-Wu); zero-mode IR '
                      'regulator y_IR=Pi/T^2 (log cut and Gaussian smoothing in M^2).'),
           'mu_over_m_v_scan': list(MU_FACTORS), 'IR_factor_scan': list(IR_FACTORS)}
    old_rows = {r['T_GeV']: r for r in old['rows']}
    rows = []
    for T in TEMPERATURES:
        t1 = time.time()
        vT = v*sqrt(1 - c*T*T/(lam*v*v)); r, tau = v/vT, T/vT
        thermal = T >= THERMAL_FROM
        tab = None
        if T >= 1000.:
            tab = w2.ThermalTables(-lam*v*v/T**2*1.02, lam*(3*(1.8*vT)**2 - v*v)/T**2)
        if thermal:
            spline = wc.ThermalSpline(-lam*r*r/tau**2, lam*(3*1.6**2 - r*r)/tau**2, with_J=True)
            base = wc.Corrected(lam, r=r, tau=tau, parts=('cw', 'heavy', 'thermal1'), heavy=(A0, A2), spline=spline)
        else:
            base = wc.Corrected(lam, r=r, tau=tau, parts=('cw', 'heavy', 'thermal1_removal'), heavy=(A0, A2))

        def reduced(tp, extra=None):
            kn, sm = w2.singular_points(tp, vT)
            f = tp.delta if extra is None else (lambda ph: tp.delta(ph) + extra(ph))
            return w2.ReducedTwoLoop(base, f, vT, lam, kn, smooth=sm)
        tp = w2.TwoLoopPotential(lam, v, T, tables=tab, thermal=thermal)
        pot = reduced(tp)
        scale_v = lam*vT**4
        # band potentials
        tps_mu = [w2.TwoLoopPotential(lam, v, T, tables=tab, thermal=thermal, mu=MV*f) for f in MU_FACTORS]
        D_mu = [(lambda x, q=q: (q.msbar_loops(x*vT) - tp.os_loops(x*vT))/scale_v) for q in tps_mu]
        D1_mu = [(lambda x, q=q: q.one_loop_msbar_minus_os(x*vT)/scale_v) for q in tps_mu]
        alts = {}
        if thermal:
            for f in IR_FACTORS:
                alts['IR_regulator_x%g' % f] = reduced(w2.TwoLoopPotential(lam, v, T, tables=tab, yIR_factor=f))
            alts['no_resummation'] = reduced(w2.TwoLoopPotential(lam, v, T, tables=tab, resum=False))
        if T == 1000.:
            ta = w2.TwoLoopPotential(lam, v, T, tables=tab, thermal=True)
            v1t = lambda ph: T**4/(2*pi*pi)*tab.JB(ta.x(ph)/T**2).real
            alts['thermal_prescription_Re_continuation'] = reduced(ta, extra=v1t)
        sp1 = w2.spinodal_eps(base)[0]
        sp2 = w2.spinodal_eps(pot)[0]
        hi = min(sp1, sp2) - 2e-3     # two-loop U0' has IR wiggles at m^2=0 next to the spinodal
        H = radiation_H(T, gstar(T))
        row = {'T_GeV': T, 'v_T_GeV': vT, 'thermal_loops': thermal, 'spinodal_one_loop': sp1,
               'spinodal_two_loop_regulated': sp2, 'a2_GeV2': tp.a2, 'a4': tp.a4, 'y_IR': tp.yIR}
        for d, scale, Hu in ((3, vT/(sqrt(lam)*T), H/T), (4, 1/lam, H/vT)):
            s_star, S_star = wn.nucleation_threshold(d, scale, Hu)
            od = old_rows[T]['d%d' % d]
            e_tree, how = od['eps_star_tree'], od['tree_method']
            res = {'S_star': S_star, 's_star': s_star, 'eps_star_tree': e_tree,
                   'eps_star_one_loop': od['eps_star_corrected'], 'one_loop_method': od['corrected_method']}
            if how == 'bounce' and e_tree < hi:
                b1 = wc.bounce(base, e_tree, d)
                bt = wc.bounce(pot, e_tree, d)
                res['S_one_loop_at_tree_eps_recomputed'] = scale*b1['s']
                res['S_one_loop_at_tree_eps_receipt'] = od.get('S_corrected_at_tree_eps')
                res['S_two_loop_at_tree_eps'] = scale*bt['s']
                res['virial_defect_two_loop_at_tree_eps'] = bt['virial_defect']
                res['S_scale_band_at_tree_eps'] = [scale*first_order(bt, D, d) for D in D_mu]
                res['S_scale_band_half_width_at_tree_eps'] = 0.5*float(np.ptp(res['S_scale_band_at_tree_eps']))
                res['S_one_loop_scale_band_first_order_at_tree_eps'] = [scale*first_order(b1, D, d) for D in D1_mu]
                res['S_alternatives_at_tree_eps'] = {k: scale*first_order(bt, lambda x, p=p: p.delta(x) - pot.delta(x), d)
                                                     for k, p in alts.items()}
                pieces = tp.two_loop_parts
                res['S_two_loop_pieces_first_order_at_tree_eps'] = {
                    k: scale*first_order(b1, lambda x, k=k: pieces(x*vT)[k]/scale_v, d) for k in pieces(np.array([vT])).keys()}
            try:
                e2 = wc.critical_eps(pot, s_star, d, lo=.2, hi=hi)
                method = 'bounce'
            except ValueError:
                e2, method = None, 'above_bounce_bracket_near_spinodal'
            res.update({'eps_star_two_loop': e2, 'two_loop_method': method, 'eps_bracket_hi': hi})
            if e2 is not None:
                b = wc.bounce(pot, e2, d)
                ds = slope(pot, e2, d, b['s'])
                sc = [first_order(b, D, d) for D in D_mu]
                scale_hw = 0.5*float(np.ptp(sc))
                other = {k: first_order(b, lambda x, p=p: p.delta(x) - pot.delta(x), d) for k, p in alts.items()}
                MIR = 1/b['radius_core']**2
                ir1 = wc.Corrected(lam, r=r, tau=tau, parts=base.parts, heavy=(A0, A2), spline=base.spline, M_IR=MIR)
                other['one_loop_CW_IR_M_IR=1/R_core^2'] = first_order(b, lambda x: ir1.delta(x) - base.delta(x), d)
                if thermal:
                    other['IR_regulator'] = max(abs(other.pop('IR_regulator_x%g' % f)) for f in IR_FACTORS)
                width_other = sum(abs(x) for x in other.values())
                res.update({'two_loop_bounce_s': b['s'], 'virial_defect': b['virial_defect'], 'ds_deps': ds,
                            'scale_shifts_reduced_action': sc, 'scale_half_width_reduced_action': scale_hw,
                            'other_shifts_reduced_action': other, 'other_half_width_reduced_action': width_other,
                            'eps_star_scale_band': [e2 - scale_hw/abs(ds), e2 + scale_hw/abs(ds)],
                            'eps_star_total_band': [e2 - (scale_hw + width_other)/abs(ds), e2 + (scale_hw + width_other)/abs(ds)],
                            'eps_star_shift_vs_one_loop': e2/od['eps_star_corrected'] - 1})
            row['d%d' % d] = res
        e3, e4 = row['d3']['eps_star_two_loop'], row['d4']['eps_star_two_loop']
        if e3 is None:
            row['easier_channel'] = 'quantum_O4'
            row['eps_eff'] = e4
            row['eps_eff_scale_band'] = row['d4']['eps_star_scale_band']
            row['eps_eff_total_band'] = row['d4']['eps_star_total_band']
        else:
            row['easier_channel'] = 'thermal_O3' if e3 < e4 else 'quantum_O4'
            row['eps_eff'] = min(e3, e4)
            for k in ('scale', 'total'):
                b3, b4 = row['d3']['eps_star_%s_band' % k], row['d4']['eps_star_%s_band' % k]
                row['eps_eff_%s_band' % k] = [min(b3[0], b4[0]), min(b3[1], b4[1])]
        row['eps_eff_one_loop'] = old_rows[T]['eps_eff_corrected']
        row['eps_eff_tree'] = old_rows[T]['eps_eff_tree']
        rows.append(row)
        print(T, row['easier_channel'], row['eps_eff'], row['eps_eff_scale_band'], row['eps_eff_total_band'],
              'S3/T@tree', row['d3'].get('S_two_loop_at_tree_eps'), time.time() - t1, flush=True)
    out['rows'] = rows

    Ts = np.array(TEMPERATURES)

    def T_n(q, vals):
        epsA = np.array([q*wn.EPS_SPINODAL*max(0., 1 - (T/model.bias_onset_GeV)**2)*(v/r['v_T_GeV'])**3
                         for T, r in zip(Ts, rows)])
        gap = epsA - np.asarray(vals)
        if gap[0] < 0:
            return None
        k = np.flatnonzero(gap < 0)
        if not k.size:
            return float(Ts[-1])
        k = k[0]
        return float(Ts[k - 1] + (Ts[k] - Ts[k - 1])*gap[k - 1]/(gap[k - 1] - gap[k]))
    bench = []
    for q in (0.99, 0.995, 1.0):
        bench.append({'q_eps_at_T0_over_eps_sp': q,
                      'T_n_tree_GeV': T_n(q, [r['eps_eff_tree'] for r in rows]),
                      'T_n_one_loop_GeV': T_n(q, [r['eps_eff_one_loop'] for r in rows]),
                      'T_n_two_loop_GeV': T_n(q, [r['eps_eff'] for r in rows]),
                      'T_n_two_loop_scale_band_GeV': [T_n(q, [r['eps_eff_scale_band'][1] for r in rows]),
                                                      T_n(q, [r['eps_eff_scale_band'][0] for r in rows])],
                      'T_n_two_loop_total_band_GeV': [T_n(q, [r['eps_eff_total_band'][1] for r in rows]),
                                                      T_n(q, [r['eps_eff_total_band'][0] for r in rows])]})
    out['nucleation_temperature_benchmarks'] = {
        'definition': 'as in wall_nucleation_corrections: highest grid-interpolated T where q eps_sp(1-(T/3000 GeV)^2)(v/v_T)^3 reaches the easier critical bias',
        'rows': bench}
    out['S3_over_T_summary'] = [{'T_GeV': r['T_GeV'], 'eps_star_tree': r['d3']['eps_star_tree'],
                                 'S3_over_T_one_loop_at_tree_eps': r['d3'].get('S_one_loop_at_tree_eps_recomputed'),
                                 'S3_over_T_two_loop_at_tree_eps': r['d3'].get('S_two_loop_at_tree_eps'),
                                 'scale_half_width': r['d3'].get('S_scale_band_half_width_at_tree_eps'),
                                 'alternatives': r['d3'].get('S_alternatives_at_tree_eps'),
                                 'eps_star_two_loop': r['d3']['eps_star_two_loop'],
                                 'eps_star_two_loop_scale_band': r['d3'].get('eps_star_scale_band'),
                                 'eps_star_two_loop_total_band': r['d3'].get('eps_star_total_band')}
                                for r in rows if r['T_GeV'] >= 1000.]
    out['scope'] = ('Supplied spectator model, single-field reduced bounces; scalar-sector two loops only (gauge/Higgs '
                    'loops enter through kappa=1e-7 and are not added); zero-momentum OS conditions (not the pole mass); '
                    'Re of the analytically continued potential where m^2<0; zero-mode IR region regulated at the thermal '
                    'mass scale; T<=1000 GeV central keeps the Boltzmann limit of wall_nucleation_corrections; fluctuation '
                    'determinant still the declared exp(+-20) band; floating-point bounces; scale bands from first-order '
                    'action shifts of the MS-bar evaluation with one-loop matched couplings over mu in [m_v/2, 2 m_v].')
    (OUT/'wall_two_loop_thermal.json').write_text(json.dumps(rnd(out), indent=1, sort_keys=True, default=float) + '\n')
    print(json.dumps(rnd(out['nucleation_temperature_benchmarks'], 6), indent=1))
    print(json.dumps(rnd(out['S3_over_T_summary'], 6), indent=1))
    print('total', time.time() - t0)


if __name__ == '__main__':
    main()
