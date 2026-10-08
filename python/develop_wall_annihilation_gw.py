"""Annihilation-phase gravitational waves of the biased physical wall network.

Stage 1 (--simulate-scan, about 15 minutes on two processes): network-only runs
(no tensor modes) for the annihilation time versus bias, two seeds, two
switch-on times and a smaller-box control.
Stage 2 (--simulate-gw, about two hours on two processes): the same network
with linear tensor modes for an unbiased reference and three biases, two seeds.
--simulate runs both. Without a flag the cached series are analysed.
"""
from pathlib import Path
from multiprocessing import Pool
import hashlib, json, os, sys
import numpy as np
from perfectpower import wall_annihilation_gw as wa
from perfectpower import wall_network as wn
from perfectpower.dimensionful_walls import WallModel, annihilation, gw_estimate

ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT/'receipts/flavor_cosmology/wall_annihilation_gw_series.json'
RECEIPT = ROOT/'receipts/flavor_cosmology/wall_annihilation_gw.json'
BASE = dict(N=192, tau_ref=96., w_ref=2., tau_on=40., ramp=5., tau_i=10., dt=.2)
SWITCH_EPS = 4e-6
EPS_SCAN = (1.5e-6, 2.5e-6, 4e-6, 6e-6, 9e-6)
SCAN = ([dict(BASE, eps=e, seed=s) for s in (0, 1) for e in EPS_SCAN]
        + [dict(BASE, eps=0., seed=s) for s in (0, 1)]
        + [dict(BASE, eps=SWITCH_EPS, seed=0, tau_on=t) for t in (30., 50.)]
        + [dict(BASE, N=128, eps=e, seed=0) for e in (2.5e-6, 4e-6, 6e-6, 9e-6)])
GW = [dict(BASE, eps=e, seed=s) for s in (0, 1) for e in (0., 2.5e-6, 4e-6, 6e-6)]
SCAN_TAU_F, GW_TAU_F = 160., 158.
SCALING_WINDOW = (48., 96.)  # unbiased A and eps_gw averaged here (formed, not yet box-limited)
K_PRS = 1.7928  # t_ann DeltaV/sigma from wall_network.json (PRS, false fraction < 1 percent)


def _scan(kw):
    os.environ['OPENBLAS_NUM_THREADS'] = '1'
    kw = dict(kw); N = kw.pop('N')
    r = wa.evolve_biased_gw(N, tau_f=SCAN_TAU_F, gw=False, measure_every=1., **kw)
    return r


def _gw(kw):
    os.environ['OPENBLAS_NUM_THREADS'] = '1'
    kw = dict(kw); N = kw.pop('N')
    return wa.evolve_biased_gw(N, tau_f=GW_TAU_F, measure_every=4., **kw)


def _round(x):
    if isinstance(x, float):
        return float('%.7g' % x)
    if isinstance(x, list):
        return [_round(y) for y in x]
    if isinstance(x, dict):
        return {k: _round(v) for k, v in x.items()}
    return x


def simulate(stages):
    cache = json.loads(CACHE.read_text()) if CACHE.exists() else {}
    with Pool(2) as pool:
        if 'scan' in stages:
            cache['scan'] = [{'params': k, **_round(r)} for k, r in zip(SCAN, pool.map(_scan, SCAN, chunksize=1))]
            CACHE.write_text(json.dumps(cache, sort_keys=True)+'\n')
        if 'gw' in stages:
            cache['gw'] = [{'params': k, **_round(r)} for k, r in zip(GW, pool.map(_gw, GW, chunksize=1))]
            CACHE.write_text(json.dumps(cache, sort_keys=True)+'\n')


def series(run, key):
    return np.array([x[key] for x in run['rows']])


def window_mean(run, key, lo, hi):
    t = series(run, 'tau'); y = series(run, key)
    m = (t >= lo) & (t <= hi)
    return float(np.mean(y[m]))


def at(run, key, tau):
    """Linear interpolation of a series at tau."""
    return float(np.interp(tau, series(run, 'tau'), series(run, key)))


def annihilation_scan(scan, A_ref):
    rows = []
    for r in scan:
        p = r['params']
        if not p['eps']:
            continue
        t_ff, t_A = wa.annihilation_times(r['rows'], A_ref, p['tau_on'])
        t_ff10, _ = wa.annihilation_times(r['rows'], A_ref, p['tau_on'], ff_threshold=.1)
        x = r['sigma']/r['DeltaV']
        rows.append({'params': p, 'sigma': r['sigma'], 'DeltaV': r['DeltaV'], 'sigma_over_DeltaV': x,
                     'tau_false_below_1pct': t_ff, 'tau_false_below_10pct': t_ff10, 'tau_A_half': t_A,
                     'K_naive': t_ff**2/2/x, 'tau_pressure_balance_K_PRS': wa.pressure_balance_tau(r['sigma'], r['DeltaV'], K_PRS),
                     'bias_over_barrier_at_ann': r['DeltaV']/(r['lam']/4),
                     'eps_over_lam': p['eps']/r['lam'],
                     'width_at_ann': float(np.sqrt(2/r['lam'])/t_ff)})
    return rows


def fits(rows, key):
    rows = [r for r in rows if np.isfinite(r[key])]
    x = np.array([r['sigma_over_DeltaV'] for r in rows]); y = np.array([r[key] for r in rows])
    p, c, se = wa.power_law_fit(x, y)
    # Offset model t_ann=t_0+K sigma/DeltaV in cosmic time t=tau^2/2 (exponent 1 in t, 1/2 in tau asymptotically).
    M = np.vstack([x, np.ones_like(x)]).T
    (K, t0), *_ = np.linalg.lstsq(M, y**2/2, rcond=None)
    resid = y**2/2 - M@np.array([K, t0])
    return {'power_law_p': p, 'power_law_p_stderr': se, 'power_law_prefactor': c,
            'cosmic_time_exponent_from_p': 2*p,
            'offset_model': {'K': float(K), 't0': float(t0), 'tau0': float(np.sqrt(max(t0, 0)*2)),
                             'rms_relative_residual_in_t': float(np.sqrt(np.mean((resid/(y**2/2))**2)))},
            'n_points': int(len(x)), 'sigma_over_DeltaV_range': [float(x.min()), float(x.max())],
            'tau_range': [float(y.min()), float(y.max())]}


def gw_analysis(gw, A_ref, eps_scal):
    ref = {r['params']['seed']: r for r in gw if not r['params']['eps']}
    out = []
    for r in gw:
        p = r['params']
        if not p['eps']:
            continue
        u = ref[p['seed']]
        tau = series(r, 'tau')
        sig = r['sigma']
        E = series(r, 'rho_gw_avg')*tau**4          # comoving GW energy, constant for free waves
        Eu = series(u, 'rho_gw_avg')*tau**4
        Ek = series(r, 'rho_gw')*tau**4
        t_ff, t_A = wa.annihilation_times(r['rows'], A_ref, p['tau_on'])
        free = tau >= t_ff + 8.
        slope = float(np.polyfit(np.log(tau[free]), np.log(E[free]), 1)[0]) if free.sum() >= 3 else float('nan')
        slope_kin = float(np.polyfit(np.log(tau[free]), np.log(Ek[free]), 1)[0]) if free.sum() >= 3 else float('nan')
        E_on = float(np.interp(p['tau_on'], tau, E)); E_ann = float(np.interp(t_ff, tau, E)); E_end = float(E[-1])
        Eu_ann = float(np.interp(t_ff, tau, Eu))
        # efficiency at annihilation in the template convention: residual energy referred to tau_ann.
        eps_ann = E_end/t_ff**4/(A_ref**2*sig**2)
        eps_fixed = series(r, 'rho_gw')/(A_ref**2*sig**2)
        eps_fixed_u = series(u, 'rho_gw')/(A_ref**2*sig**2)
        # scaling reference: the same-seed unbiased network at the measurement nearest tau_ann
        j_a = int(np.argmin(abs(tau - t_ff)))
        sh_u_ann = wa.spectrum_shape(u['rows'][j_a]['k'], u['rows'][j_a]['drho_avg_dlnk'], tau[j_a])
        sh_ann = wa.spectrum_shape(r['rows'][j_a]['k'], r['rows'][j_a]['drho_avg_dlnk'], tau[j_a])
        s_u_ann = np.array(u['rows'][j_a]['drho_avg_dlnk'])*tau[j_a]**4
        eps_u_ann_avg = float(np.interp(t_ff, tau, series(u, 'rho_gw_avg')))/(A_ref**2*sig**2)
        eps_u_ann_kin = float(np.interp(t_ff, tau, series(u, 'rho_gw')))/(A_ref**2*sig**2)
        kin_over_avg_u = float(np.interp(t_ff, tau, series(u, 'rho_gw')/series(u, 'rho_gw_avg')))
        sh_end = wa.spectrum_shape(r['rows'][-1]['k'], r['rows'][-1]['drho_avg_dlnk'], tau[-1])
        sh_u_end = wa.spectrum_shape(u['rows'][-1]['k'], u['rows'][-1]['drho_avg_dlnk'], tau[-1])
        k_end = np.array(r['rows'][-1]['k']); s_end = np.array(r['rows'][-1]['drho_avg_dlnk'])*tau[-1]**4
        s_u_end = np.array(u['rows'][-1]['drho_avg_dlnk'])*tau[-1]**4
        out.append({'params': p, 'tau_ann_false_1pct': t_ff, 'tau_A_half': t_A,
                    'E_comoving_at_on': E_on, 'E_comoving_at_ann': E_ann, 'E_comoving_end': E_end,
                    'E_unbiased_at_ann': Eu_ann, 'E_unbiased_end': float(Eu[-1]),
                    'E_at_on_over_E_end': E_on/E_end,
                    'collapse_excess_over_unbiased_at_ann': E_end/Eu_ann - 1,
                    'eps_unbiased_at_ann_avg_fixedA': eps_u_ann_avg, 'eps_unbiased_at_ann_kin_fixedA': eps_u_ann_kin,
                    'unbiased_kin_over_avg_at_ann': kin_over_avg_u,
                    'fraction_of_final_made_after_ann': 1 - E_ann/E_end,
                    'biased_over_unbiased_at_ann': E_ann/Eu_ann,
                    'biased_end_over_unbiased_at_ann': E_end/Eu_ann,
                    'eps_ann_template': eps_ann, 'eps_ann_over_scaling': eps_ann/eps_scal,
                    'eps_fixedA_max_biased': float(eps_fixed[tau > p['tau_on']].max()),
                    'eps_fixedA_unbiased_at_same_tau': float(eps_fixed_u[np.argmax(np.where(tau > p['tau_on'], eps_fixed, -1))]),
                    'free_propagation': {'from_tau': float(t_ff + 8.), 'to_tau': float(tau[-1]), 'n': int(free.sum()),
                                         'dlnE_avg_dlntau': slope, 'dlnE_kin_dlntau': slope_kin,
                                         'E_avg_rel_spread': float(np.std(E[free])/np.mean(E[free])) if free.sum() else float('nan')},
                    'spectrum_unbiased_at_ann': sh_u_ann, 'spectrum_biased_at_ann': sh_ann,
                    'spectrum_end': sh_end, 'spectrum_unbiased_end': sh_u_end,
                    'peak_k_ratio_end_over_unbiased_at_ann': sh_end['peak_k']/sh_u_ann['peak_k'],
                    'spectral_ratio_end_over_unbiased_at_ann': (s_end/np.where(s_u_ann > 0, s_u_ann, np.nan)).tolist(),
                    'band_ratio_end_over_unbiased_at_ann': {name: float(s_end[(k_end >= lo) & (k_end < hi)].sum()/s_u_ann[(k_end >= lo) & (k_end < hi)].sum())
                                                            for name, lo, hi in (('k<0.1', 0, .1), ('0.1<=k<0.5', .1, .5), ('0.5<=k<pi/2', .5, np.pi/2), ('k>=pi/2', np.pi/2, 9.))},
                    'peak_f_over_H_ann': sh_end['peak_k']*t_ff/(2*np.pi),
                    'box_f_over_H_ann': k_end[0]*t_ff/(2*np.pi),
                    'spectral_ratio_biased_over_unbiased_end': (s_end/np.where(s_u_end > 0, s_u_end, np.nan)).tolist(),
                    'k': k_end.tolist(),
                    'series': {'tau': tau.tolist(), 'A': series(r, 'A').tolist(), 'false_fraction': series(r, 'false_fraction').tolist(),
                               'E_avg': E.tolist(), 'E_kin': Ek.tolist(), 'E_unbiased_avg': Eu.tolist(),
                               'eps_fixedA': eps_fixed.tolist(), 'eps_fixedA_unbiased': eps_fixed_u.tolist()}})
    return out


def main():
    stages = {s for s in ('scan', 'gw') if '--simulate' in sys.argv or '--simulate-'+s in sys.argv}
    if stages or not CACHE.exists():
        simulate(stages or {'scan', 'gw'})
    cache = json.loads(CACHE.read_text())
    scan, gw = cache['scan'], cache['gw']
    out = {'model': ('V=(lam/4)(phi^2-1)^2+eps s(tau)(phi^3/3-phi): minima exactly at phi=+-1 for eps<lam, Delta V=4 eps/3, '
                     'phi=+1 true vacuum; s(tau) C^1 smoothstep from tau_on to tau_on+5; eps constant physical bias.'),
           'method': ('Physical radiation-era equation phi\'\'+2phi\'/tau-lap phi=-tau^2 dV/dphi with a=tau, lam=2/(w_ref tau_ref)^2 '
                      '(comoving width 2 at tau=96), N=192 (control N=128), dx=1, dt=0.2, tau_i=10, Gaussian initial field rms 0.1 '
                      '(wall_network.initial_field), float32; tensor modes u_ij\'\'+2u_ij\'/tau-lap u_ij=16 pi G d_i phi d_j phi, TT projected; '
                      'rho_gw=<h\'h\'>/(32 pi G a^2) and rho_avg=(<h\'h\'>+<grad h grad h>)/(64 pi G a^2) with lattice k_eff.'),
           'series_cache': {'path': os.path.relpath(CACHE, ROOT), 'sha256': hashlib.sha256(CACHE.read_bytes()).hexdigest()}}
    # unbiased reference: A and eps_gw over the scaling window
    unb_scan = [r for r in scan if not r['params']['eps']]
    unb_gw = [r for r in gw if not r['params']['eps']]
    A_ref = float(np.mean([window_mean(r, 'A', *SCALING_WINDOW) for r in unb_scan]))
    sigma = unb_gw[0]['sigma']
    eps_scal = [float(np.mean(series(r, 'rho_gw')[(series(r, 'tau') >= SCALING_WINDOW[0]) & (series(r, 'tau') <= SCALING_WINDOW[1])]
                              / (series(r, 'A')[(series(r, 'tau') >= SCALING_WINDOW[0]) & (series(r, 'tau') <= SCALING_WINDOW[1])]**2*sigma**2)))
                for r in unb_gw]
    eps_scal_fixed = [window_mean(r, 'rho_gw', *SCALING_WINDOW)/(A_ref**2*sigma**2) for r in unb_gw]
    out['unbiased_reference'] = {'scaling_window_tau': list(SCALING_WINDOW), 'A_ref': A_ref,
                                 'A_window_by_seed': [window_mean(r, 'A', *SCALING_WINDOW) for r in unb_scan],
                                 'A_final_by_seed': [float(series(r, 'A')[-1]) for r in unb_scan],
                                 'eps_gw_window_by_seed': eps_scal, 'eps_gw_window_fixedA_by_seed': eps_scal_fixed,
                                 'lam': unb_gw[0]['lam'], 'sigma': sigma}
    eps_s = float(np.mean(eps_scal))
    # (1) annihilation time versus bias
    ann = annihilation_scan(scan, A_ref)
    main_rows = [r for r in ann if r['params']['N'] == BASE['N'] and r['params']['tau_on'] == BASE['tau_on']]
    out['annihilation'] = {'runs': ann,
                           'expected_exponent': {'p_conformal': .5, 'p_cosmic': 1.,
                                                 'derivation': 'rho_wall=A sigma/t (scaling), annihilation when DeltaV ~ C_ann rho_wall: t_ann=C_ann A sigma/DeltaV=K sigma/DeltaV; a=tau gives t=tau^2/2, so tau_ann=(2K sigma/DeltaV)^(1/2).'},
                           'fit_false_1pct': fits(main_rows, 'tau_false_below_1pct'),
                           'fit_false_10pct': fits(main_rows, 'tau_false_below_10pct'),
                           'fit_A_half': fits([r for r in main_rows if np.isfinite(r['tau_A_half'])], 'tau_A_half'),
                           'fit_false_1pct_seed0': fits([r for r in main_rows if r['params']['seed'] == 0], 'tau_false_below_1pct'),
                           'fit_false_1pct_seed1': fits([r for r in main_rows if r['params']['seed'] == 1], 'tau_false_below_1pct'),
                           'fit_N128_box_control': fits([r for r in ann if r['params']['N'] != BASE['N']], 'tau_false_below_1pct'),
                           'switch_on_control': [{'tau_on': r['params']['tau_on'], 'tau_false_below_1pct': r['tau_false_below_1pct']}
                                                 for r in ann if r['params']['eps'] == SWITCH_EPS and r['params']['seed'] == 0 and r['params']['N'] == BASE['N']],
                           'K_PRS_reference': K_PRS}
    # (2,3) GW through and after annihilation
    g = gw_analysis(gw, A_ref, eps_s)
    out['gw'] = {'runs': g, 'eps_gw_scaling_mean': eps_s}
    keys = ('biased_over_unbiased_at_ann', 'biased_end_over_unbiased_at_ann', 'collapse_excess_over_unbiased_at_ann',
            'fraction_of_final_made_after_ann', 'E_at_on_over_E_end', 'eps_ann_template', 'eps_unbiased_at_ann_avg_fixedA',
            'unbiased_kin_over_avg_at_ann', 'peak_k_ratio_end_over_unbiased_at_ann', 'peak_f_over_H_ann')
    out['gw']['summary'] = {k: [float(np.min([r[k] for r in g])), float(np.max([r[k] for r in g]))] for k in keys}
    out['gw']['summary'].update({
        'eps_ann_template_mean': float(np.mean([r['eps_ann_template'] for r in g])),
        'UV_slope_end': [float(np.min([r['spectrum_end']['UV_slope'] for r in g])), float(np.max([r['spectrum_end']['UV_slope'] for r in g]))],
        'UV_slope_unbiased_at_ann': [float(np.min([r['spectrum_unbiased_at_ann']['UV_slope'] for r in g])), float(np.max([r['spectrum_unbiased_at_ann']['UV_slope'] for r in g]))],
        'UV_slope_biased_at_ann': [float(np.min([r['spectrum_biased_at_ann']['UV_slope'] for r in g])), float(np.max([r['spectrum_biased_at_ann']['UV_slope'] for r in g]))],
        'peak_bin_unbiased_at_ann': [r['spectrum_unbiased_at_ann']['peak_bin'] for r in g],
        'band_ratio_end_over_unbiased_at_ann': {b: [float(min(r['band_ratio_end_over_unbiased_at_ann'][b] for r in g)), float(max(r['band_ratio_end_over_unbiased_at_ann'][b] for r in g))]
                                                for b in g[0]['band_ratio_end_over_unbiased_at_ann']},
        'enhancement_mean': float(np.mean([r['biased_end_over_unbiased_at_ann'] for r in g])),
        'IR_slope_end': [r['spectrum_end']['IR_slope'] for r in g],
        'peak_bin_end': [r['spectrum_end']['peak_bin'] for r in g],
        'free_dlnE_avg_dlntau': [r['free_propagation']['dlnE_avg_dlntau'] for r in g],
        'free_dlnE_kin_dlntau': [r['free_propagation']['dlnE_kin_dlntau'] for r in g],
        'free_E_avg_rel_spread': [r['free_propagation']['E_avg_rel_spread'] for r in g]})

    # Template comparison (declared conditional model of dimensionful_walls)
    old = json.loads((ROOT/'receipts/flavor_cosmology/dimensionful_walls.json').read_text())
    model = WallModel(**old['declared_model_inputs'])
    sig_phys = json.loads((ROOT/'receipts/flavor_cosmology/wall_stability.json').read_text())['three_field_wall']['tension_GeV3']
    prev = json.loads((ROOT/'receipts/flavor_cosmology/wall_gw.json').read_text())['declared_cosmology_update']
    Akey = prev['lattice']['A']
    def tmpl(K, eps, x):
        a = annihilation(model, sig_phys, area=Akey, annihilation_factor=K/Akey)
        e = gw_estimate(sig_phys, a['H_GeV'], area=Akey, efficiency=eps, peak_frequency_in_H=x, frequencies=np.array([1e-9]))
        return {'K': K, 'efficiency': eps, 'peak_f_over_H': x, 'T_ann_GeV': a['temperature_GeV'],
                'peak_frequency_Hz': e['peak_frequency_Hz'], 'peak_Omega_h2': e['peak_Omega_h2']}
    K_off = out['annihilation']['fit_false_1pct']['offset_model']['K']
    # Template efficiency: the scaling (kinetic-convention) efficiency of wall_gw.json times the measured
    # collapse enhancement E_end/E_unbiased(tau_ann), a ratio of like quantities in one convention.
    enh = out['gw']['summary']['biased_end_over_unbiased_at_ann']
    eps0 = prev['lattice']['efficiency']
    eps_a = [eps0*enh[0], eps0*enh[1]]
    xs = out['gw']['summary']['peak_f_over_H_ann']
    out['gw']['summary']['template_efficiency_from_enhancement'] = eps_a
    out['template_comparison'] = {
        'previous_lattice_update': prev['lattice'],
        'this_work_central': tmpl(K_off, eps0*out['gw']['summary']['enhancement_mean'], prev['lattice']['peak_f_over_H']),
        'declared': prev['declared'],
        'corners': [tmpl(K, e, x) for K in (K_off, K_PRS) for e in eps_a for x in xs],
        'scope': ('Same classical pressure-balance and redshift template (dimensionful_walls.annihilation, gw_estimate). K from the '
                  'offset fit of the physical runs (t_ann-t_0=K sigma/DeltaV; the offset is dropped because the physical bias '
                  'acts for ~1e25 Hubble times) or the PRS K; efficiency = wall_gw scaling efficiency x measured collapse '
                  'enhancement 1.42-1.53; peak f/H only bounded by the box. A drops out of T_ann at fixed K; the template IR '
                  'slope remains the causal f^3 input.')}
    out['scope'] = ('Linear tensor modes on a periodic 192^3 lattice (128^3 control) of the physical radiation-era phi^4 network with a '
                    'cubic bias switched on at tau=40; formation near tau=40, annihilation between tau~80 and ~130, so the scaling '
                    'phase before the bias acts is short and the free-propagation window after annihilation is 20-70 units of tau. '
                    'GW production itself starts only near tau=50, so the scaling reference is the same-seed unbiased run. '
                    'Two seeds, bias/barrier ratios Delta V/(lam/4)=0.15-0.89, walls 1.3-2.3 lattice spacings thick at annihilation; '
                    'GW spectral peaks within one or two bins of the box mode. '
                    'No backreaction, no expansion-history change from the walls, float32, not certified.')
    RECEIPT.write_text(json.dumps(out, indent=1, sort_keys=True, default=float)+'\n')
    a = out['annihilation']
    for k in ('fit_false_1pct', 'fit_false_10pct', 'fit_A_half', 'fit_N128_box_control', 'fit_false_1pct_seed0', 'fit_false_1pct_seed1'):
        print(k, json.dumps(a[k]))
    for r in ann:
        print(r['params']['N'], r['params']['seed'], r['params']['eps'], r['params']['tau_on'], 'tau1%%=%.1f tau10%%=%.1f tauA=%.1f pb=%.1f K=%.2f b/B=%.3f w=%.2f' % (
            r['tau_false_below_1pct'], r['tau_false_below_10pct'], r['tau_A_half'], r['tau_pressure_balance_K_PRS'], r['K_naive'],
            r['bias_over_barrier_at_ann'], r['width_at_ann']))
    print(json.dumps(out['unbiased_reference']))
    for r in g:
        print({k: v for k, v in r.items() if k not in ('series', 'spectral_ratio_biased_over_unbiased_end', 'k')})
    print(json.dumps(out['gw']['summary'], indent=1))
    print(json.dumps(out['template_comparison']['this_work_central']), json.dumps(prev['lattice']))
    for c in out['template_comparison']['corners']:
        print(json.dumps(c))
    print(json.dumps(prev['declared']))


if __name__ == '__main__':
    main()
