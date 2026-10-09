"""Asymptotic annihilation law and GW peak of the lattice wall network (PRS s-family).

Stage ann (--simulate-ann): network-only runs at 320^3 (192^3 box control) for
s = 0, 0.5, 1 over a factor 28 in X = sigma/Delta V, several seeds, plus width
and switch-on controls; about 3-4 hours on one process.
Stage gw (--simulate-gw): tensor-mode runs of the unbiased network, s=0 at
N = 192, 256 (two seeds), 320 and s=0.5 at 256; about 3 hours on one process,
peak memory about 5 GB (320^3).
Both stages are resumable (finished runs are kept in their cache files) and
write separate caches, so they can run as two concurrent processes.
--workers n uses n processes for a stage (default 1). Without flags the cached
series are analysed into receipts/flavor_cosmology/wall_network_asymptotic.json.
"""
from pathlib import Path
from multiprocessing import Pool
import hashlib, json, os, sys
import numpy as np
from perfectpower import wall_network_asymptotic as wna
from perfectpower import wall_annihilation_gw as wa

ROOT = Path(__file__).resolve().parents[1]
RC = ROOT/'receipts/flavor_cosmology'
CACHE_ANN = RC/'wall_network_asymptotic_ann_series.json'
CACHE_GW = RC/'wall_network_asymptotic_gw_series.json'
RECEIPT = RC/'wall_network_asymptotic.json'
NET = RC/'wall_network.json'
PREV = RC/'wall_annihilation_gw.json'
WALL_GW = RC/'wall_gw.json'

STOP = .002  # runs end once min(f,1-f) < 0.2 percent
S0 = dict(N=320, s=0., w_ref=2., tau_ref=1., tau_on=4., ramp=4., tau_f=240.)
S05 = dict(N=320, s=.5, w_ref=2., tau_ref=160., tau_on=24., ramp=4., tau_f=240.)
S1 = dict(N=320, s=1., w_ref=2., tau_ref=160., tau_on=40., ramp=5., tau_f=240.)
X_S0 = (240., 420., 800., 1480., 2630., 4450., 6700.)
X_S05 = (660., 1100., 1800., 3000., 4500., 6700.)
X_S1 = (1000., 1600., 2600., 4400., 6700.)
# Runs are executed in list order (memory: the 384^3 network runs come first, the 320^3 tensor run last).
ANN = ([dict(S0, N=384, X=X, seed=0) for X in X_S0[4:]]
       + [dict(S0, X=X, seed=sd) for sd in (0, 1, 2) for X in X_S0]
       + [dict(S0, X=None, seed=sd, tau_f=160.) for sd in (0, 1)]
       + [dict(S0, N=256, X=X, seed=0) for X in X_S0]
       + [dict(S0, w_ref=3., X=X, seed=0) for X in X_S0[2:6]]
       + [dict(S0, tau_on=12., X=X, seed=0) for X in (420., 1480., 4450.)]
       + [dict(S05, X=X, seed=sd) for sd in (0, 1) for X in X_S05]
       + [dict(S05, X=None, seed=0, tau_f=160.)]
       + [dict(S1, X=X, seed=0) for X in X_S1]
       + [dict(S1, X=None, seed=0, tau_f=160.)])
GW = [dict(N=192, s=0., w_ref=2., tau_ref=1., seed=0, tau_f=96.),
      dict(N=256, s=0., w_ref=2., tau_ref=1., seed=1, tau_f=128.),
      dict(N=320, s=0., w_ref=2., tau_ref=1., seed=0, tau_f=160.),
      dict(N=256, s=.5, w_ref=2., tau_ref=128., seed=0, tau_f=128.)]
A_WINDOW = {0.: (30., 120.), .5: (40., 120.), 1.: (60., 120.)}  # unbiased A averaged here
B_CUT = .35  # asymptotic subset: bias/barrier at annihilation below this
K_PRS = 1.7928  # C_ann*A of wall_network.json
A_PRS = 0.8066632731431248  # area_parameter.A of wall_network.json (so C_ann,PRS = K_PRS/A_PRS)


def key(p):
    return json.dumps(p, sort_keys=True)


def _round(x):
    if isinstance(x, float):
        return float('%.7g' % x)
    if isinstance(x, list):
        return [_round(y) for y in x]
    if isinstance(x, dict):
        return {k: _round(v) for k, v in x.items()}
    return x


def _ann(p):
    os.environ['OPENBLAS_NUM_THREADS'] = '1'
    kw = dict(p); N = kw.pop('N')
    r = wna.evolve(N, measure_every=1., stop_false_fraction=STOP if kw['X'] else None, **kw)
    rows = r.pop('rows')
    cols = {c: [x[c] for x in rows] for c in ('tau', 'A', 'false_fraction', 'bias_over_barrier')}
    return p, _round(dict(r, **cols))


def _gw(p):
    os.environ['OPENBLAS_NUM_THREADS'] = '1'
    kw = dict(p); N = kw.pop('N')
    r = wna.evolve(N, gw=True, measure_every=2., gw_every=4., **kw)
    return p, _round(r)


def simulate(stage, workers):
    cache_path, runs, fn = (CACHE_ANN, ANN, _ann) if stage == 'ann' else (CACHE_GW, GW, _gw)
    cache = json.loads(cache_path.read_text()) if cache_path.exists() else {}
    todo = [p for p in runs if key(p) not in cache]
    with Pool(workers) as pool:
        for p, r in pool.imap_unordered(fn, todo, chunksize=1):
            cache[key(p)] = r
            cache_path.write_text(json.dumps(cache, sort_keys=True, separators=(',', ':'))+'\n')
            print('done', key(p), flush=True)


# --- analysis ------------------------------------------------------------------

def cross(tau, y, level, after):
    tau, y = np.asarray(tau), np.asarray(y)
    m = np.flatnonzero((tau > after) & (y < level))
    if not m.size:
        return float('nan')
    j = m[0]
    if j == 0 or y[j - 1] < level:
        return float(tau[j])
    return float(tau[j - 1] + (y[j - 1] - level)/(y[j - 1] - y[j])*(tau[j] - tau[j - 1]))


def ann_rows(cache):
    unb = {}
    for k, r in cache.items():
        p = json.loads(k)
        if p['X'] is None:
            lo, hi = A_WINDOW[p['s']]
            t, A = np.array(r['tau']), np.array(r['A'])
            unb.setdefault(p['s'], []).append(float(A[(t >= lo) & (t <= hi)].mean()))
    A_ref = {s: float(np.mean(v)) for s, v in unb.items()}
    # seed-averaged unbiased A(tau) of each s (N=320, w_ref=2), for C_ann = t_ann DeltaV/(A(t_ann) sigma)
    curves = {}
    for k, r in cache.items():
        p = json.loads(k)
        if p['X'] is None:
            curves.setdefault(p['s'], []).append((np.array(r['tau']), np.array(r['A'])))
    A_curve = {}
    for s, cs in curves.items():
        t = cs[0][0][:min(len(c[0]) for c in cs)]
        A_curve[s] = (t, np.mean([c[1][:len(t)] for c in cs], axis=0))
    out = []
    for k, r in cache.items():
        p = json.loads(k)
        if p['X'] is None:
            continue
        t = np.array(r['tau']); ff = np.minimum(r['false_fraction'], 1 - np.array(r['false_fraction']))
        t1 = cross(t, ff, .01, p['tau_on']); t10 = cross(t, ff, .1, p['tau_on'])
        tA = cross(t, r['A'], .5*A_ref.get(p['s'], float('nan')), p['tau_on'])
        bb = float(np.interp(t1, t, r['bias_over_barrier'])) if np.isfinite(t1) else float('nan')
        if p['s'] in A_curve and np.isfinite(t1):
            tc, Ac = A_curve[p['s']]
            Aa = float(np.interp(t1, tc, Ac)) if t1 <= tc[-1] else float('nan')
        else:
            Aa = float('nan')
        out.append({'params': p, 'X': p['X'], 'tau_false_1pct': t1, 'tau_false_10pct': t10, 'tau_A_half': tA,
                    'bias_over_barrier_at_ann': bb, 'K_naive': t1**2/2/p['X'],
                    'A_unbiased_at_ann': Aa, 'C_ann': t1**2/2/p['X']/Aa,
                    'width_at_ann': float(np.sqrt(2/r['lam'])*t1**(-p['s'])) if np.isfinite(t1) else float('nan')})
    out.sort(key=lambda x: (x['params']['s'], x['params']['N'], x['params']['w_ref'], x['params']['tau_on'], x['params']['seed'], x['X']))
    return A_ref, out


def select(rows, **kw):
    return [r for r in rows if all(r['params'][k] == v for k, v in kw.items())]


def fit_block(rows, crit='tau_false_1pct', bcut=None):
    rows = [r for r in rows if np.isfinite(r[crit]) and (bcut is None or r['bias_over_barrier_at_ann'] <= bcut)]
    if len(rows) < 3:
        return {'n_points': len(rows)}
    X = np.array([r['X'] for r in rows]); y = np.array([r[crit] for r in rows])
    p, c, se = wna.fit_power(X, y)
    K, t0, Kse = wna.fit_offset(X, y)
    q, Kq, t0q = wna.fit_power_with_offset(X, y)
    return {'n_points': len(rows), 'X_range': [float(X.min()), float(X.max())], 'tau_range': [float(y.min()), float(y.max())],
            'p': p, 'p_stderr': se, 'prefactor': c, 'K_if_p_half': float(np.mean(y**2/2/X)),
            'offset_fit': {'K': K, 'K_stderr': Kse, 't0': t0},
            'power_with_offset_fit': {'q_cosmic': q, 'p_equiv': q/2, 'K': Kq, 't0': t0q}}


def seed_spread(rows, crit='tau_false_1pct', bcut=None):
    """Per-seed fits; p and K reported as mean and standard error over seeds."""
    seeds = sorted({r['params']['seed'] for r in rows})
    fs = [fit_block([r for r in rows if r['params']['seed'] == s], crit, bcut) for s in seeds]
    fs = [f for f in fs if f.get('n_points', 0) >= 3]
    if len(fs) < 2:
        return {'n_seeds': len(fs)}
    ps = np.array([f['p'] for f in fs]); Ks = np.array([f['offset_fit']['K'] for f in fs])
    Kh = np.array([f['K_if_p_half'] for f in fs])
    return {'n_seeds': len(fs), 'p_by_seed': ps.tolist(), 'p_mean': float(ps.mean()), 'p_sem': float(ps.std(ddof=1)/np.sqrt(len(ps))),
            'K_offset_by_seed': Ks.tolist(), 'K_offset_mean': float(Ks.mean()), 'K_offset_sem': float(Ks.std(ddof=1)/np.sqrt(len(Ks))),
            'K_if_p_half_by_seed': Kh.tolist()}


def local_table(rows, crit='tau_false_1pct'):
    """Successive slopes d ln tau/d ln X computed seed by seed (same initial field at every X),
    then the mean over seeds and its standard error."""
    X = sorted({r['X'] for r in rows if np.isfinite(r[crit])})
    seeds = sorted({r['params']['seed'] for r in rows})
    val = {(r['params']['seed'], r['X']): r[crit] for r in rows if np.isfinite(r[crit])}
    out = []
    for i in range(len(X) - 1):
        dl = np.log(X[i + 1]/X[i])
        sl = [np.log(val[(s, X[i + 1])]/val[(s, X[i])])/dl for s in seeds if (s, X[i]) in val and (s, X[i + 1]) in val]
        tm = [val[(s, x)] for s in seeds for x in (X[i], X[i + 1]) if (s, x) in val]
        out.append({'X_mid': float(np.sqrt(X[i]*X[i + 1])), 'tau_mid': float(np.exp(np.mean(np.log(tm)))),
                    'p_local': float(np.mean(sl)), 'n_seeds': len(sl),
                    'p_local_sem': float(np.std(sl, ddof=1)/np.sqrt(len(sl))) if len(sl) > 1 else float('nan'),
                    'p_local_by_seed': [float(x) for x in sl]})
    return out


def _ratio(rows, ref, X, **kw):
    a = select(rows, X=X, **kw); b = select(ref, X=X, seed=0)
    if not a or not b:
        return None
    return float(a[0]['tau_false_1pct']/b[0]['tau_false_1pct'])


def _p_seed0(rows, Xs):
    rr = [r for r in rows if r['X'] in Xs and r['params']['seed'] == 0 and np.isfinite(r['tau_false_1pct'])]
    if len(rr) < 2:
        return float('nan')
    return wna.fit_power([r['X'] for r in rr], [r['tau_false_1pct'] for r in rr])[0]


def controls_s0(rows, main0):
    """Box (N=256, 384), width (w_ref=3) and switch-on (tau_on=12) controls against the N=320 seed-0 runs."""
    out = {}
    for name, kw, Xs in (('box_N256', dict(s=0., N=256, w_ref=2., tau_on=4.), X_S0),
                         ('box_N384', dict(s=0., N=384, w_ref=2., tau_on=4.), X_S0[4:]),
                         ('width_w3', dict(s=0., N=320, w_ref=3., tau_on=4.), X_S0[2:6]),
                         ('switch_on_tau12', dict(s=0., N=320, w_ref=2., tau_on=12.), (420., 1480., 4450.))):
        rr = select(rows, **kw)
        have = [X for X in Xs if select(rr, X=X)]
        if not have:
            out[name] = {'n_runs': 0}
            continue
        Xa = [X for X in have if X >= 1480.]
        out[name] = {'n_runs': len(have), 'X': have,
                     'tau_ratio_over_N320_w2_on4_seed0': [_ratio(rr, main0, X) for X in have],
                     'p_control': _p_seed0(rr, have), 'p_reference_same_X_seed0': _p_seed0(main0, have),
                     'p_control_X_ge_1480': _p_seed0(rr, Xa), 'p_reference_X_ge_1480_seed0': _p_seed0(main0, Xa)}
    return out


def verdict_s0(main0, ctrl, A_ref0):
    """The asymptotic exponent of the s=0 (earliest-formation) family with statistical and systematic errors."""
    sub = [r for r in main0 if r['bias_over_barrier_at_ann'] <= B_CUT]
    ss = seed_spread(main0, bcut=B_CUT)
    if ss.get('n_seeds', 0) < 2:
        return {'n_seeds': ss.get('n_seeds', 0)}
    syst = {}
    for name, keyc, keyr in (('box_N384', 'p_control', 'p_reference_same_X_seed0'),
                             ('box_N256', 'p_control_X_ge_1480', 'p_reference_X_ge_1480_seed0'),
                             ('width_w3', 'p_control_X_ge_1480', 'p_reference_X_ge_1480_seed0')):
        c = ctrl.get(name, {})
        if c.get('n_runs') and np.isfinite(c.get(keyc, np.nan)) and np.isfinite(c.get(keyr, np.nan)):
            syst[name] = float(c[keyc] - c[keyr])
    sys_tot = float(np.sqrt(sum(v*v for v in syst.values()))) if syst else float('nan')
    stat = ss['p_sem']
    p = ss['p_mean']
    tot = float(np.hypot(stat, sys_tot)) if np.isfinite(sys_tot) else stat
    Kh = np.array([r['K_naive'] for r in sub]); Ca = np.array([r['C_ann'] for r in sub if np.isfinite(r['C_ann'])])
    return {'subset': 'N=320, w_ref=2, tau_on=4, bias/barrier at annihilation <= %g' % B_CUT,
            'n_points': len(sub), 'X_range': [min(r['X'] for r in sub), max(r['X'] for r in sub)],
            'p_mean_over_seeds': p, 'p_stat_sem': stat, 'p_systematic_shifts': syst, 'p_systematic_quadrature': sys_tot,
            'p_total_error': tot, 'deviation_from_half_in_total_sigma': float((p - .5)/tot),
            'K_naive_t_ann_over_X': {'mean': float(Kh.mean()), 'sd': float(Kh.std(ddof=1)), 'range': [float(Kh.min()), float(Kh.max())]},
            'C_ann_with_unbiased_A_at_t_ann': ({'mean': float(Ca.mean()), 'sd': float(Ca.std(ddof=1)), 'n': int(Ca.size)} if Ca.size > 1 else None),
            'A_ref_s0': A_ref0, 'K_over_K_PRS': float(Kh.mean()/K_PRS),
            'K_over_C_ann_PRS_times_A_ref_s0': float(Kh.mean()/(K_PRS/A_PRS*A_ref0)) if A_ref0 else None}


def gw_analysis(cache):
    out = []
    for k, r in cache.items():
        p = json.loads(k)
        series = []
        for x in r['rows']:
            if 'k' not in x:
                continue
            tau = x['tau']
            sh = wna.spectrum_shape(x['k'], x['drho_avg_dlnk'], tau)
            shk = wna.spectrum_shape(x['k'], x['drho_dlnk'], tau)
            kk = np.array(x['k']); sp = np.array(x['drho_avg_dlnk'])
            good = sp > 0
            kk, sp = kk[good], sp[good]
            # IR slopes split at k tau = 1 (super-horizon, causal region) and between there and k_peak/1.5
            sup = kk*tau <= 1.
            sub = (kk*tau > 1.) & (kk <= sh['peak_k']/1.5)
            fit = lambda m: float(np.polyfit(np.log(kk[m]), np.log(sp[m]), 1)[0]) if m.sum() >= 3 else float('nan')
            series.append({'tau': tau, 'A': x['A'], 'eps_gw_kin': x['rho_gw']/(x['A']**2*r['sigma0']**2),
                           'eps_gw_avg': x['rho_gw_avg']/(x['A']**2*r['sigma0']**2),
                           'peak_f_over_H': sh['peak_f_over_H'], 'peak_bin': sh['peak_bin'], 'peak_over_box': sh['peak_over_box'],
                           'peak_f_over_H_parabola': sh['peak_f_over_H_parabola'],
                           'peak_f_over_H_kin': shk['peak_f_over_H'],
                           'box_f_over_H': float(np.array(x['k'])[0]*tau/(2*np.pi)),
                           'IR_slope_all': sh['IR_slope'], 'n_ir_bins': sh['n_ir_bins'], 'UV_slope': sh['UV_slope'],
                           'IR_slope_superhorizon': fit(sup), 'n_superhorizon_bins': int(sup.sum()),
                           'IR_slope_subhorizon': fit(sub), 'n_subhorizon_ir_bins': int(sub.sum())})
        out.append({'params': p, 'lam': r['lam'], 'sigma0': r['sigma0'], 'series': series})
    out.sort(key=lambda x: (x['params']['s'], x['params']['N'], x['params']['seed']))
    return out


def gw_summary(g, s=0., tmin=None, peak_over_box_min=3.):
    """Measurements of formed s networks with the peak at least peak_over_box_min times the box mode."""
    rows = [x for r in g if r['params']['s'] == s for x in r['series']
            if (tmin is None or x['tau'] >= tmin) and x['peak_over_box'] >= peak_over_box_min]
    if not rows:
        return {'n': 0}
    f = np.array([x['peak_f_over_H'] for x in rows])
    def stat(key, nkey=None):
        v = np.array([x[key] for x in rows if np.isfinite(x[key]) and (nkey is None or x[nkey] >= 3)])
        return {'mean': float(v.mean()), 'std': float(v.std()), 'n': int(v.size), 'range': [float(v.min()), float(v.max())]} if v.size else {'n': 0}
    return {'n': len(rows), 'tau_range': [float(min(x['tau'] for x in rows)), float(max(x['tau'] for x in rows))],
            'peak_f_over_H': {'mean': float(f.mean()), 'std': float(f.std()), 'range': [float(f.min()), float(f.max())]},
            'peak_f_over_H_parabola': stat('peak_f_over_H_parabola'),
            'eps_gw_kin': stat('eps_gw_kin'), 'eps_gw_avg': stat('eps_gw_avg'),
            'IR_slope_all_bins_below_peak': stat('IR_slope_all', 'n_ir_bins'),
            'IR_slope_superhorizon': stat('IR_slope_superhorizon', 'n_superhorizon_bins'),
            'IR_slope_subhorizon': stat('IR_slope_subhorizon', 'n_subhorizon_ir_bins'),
            'UV_slope': stat('UV_slope')}


def main():
    workers = int(sys.argv[sys.argv.index('--workers') + 1]) if '--workers' in sys.argv else 1
    for stage in ('ann', 'gw'):
        if '--simulate' in sys.argv or '--simulate-'+stage in sys.argv:
            simulate(stage, workers)
    if '--simulate-ann' in sys.argv or '--simulate-gw' in sys.argv:
        if not (CACHE_ANN.exists() and CACHE_GW.exists()):
            return
    cache = json.loads(CACHE_ANN.read_text())
    gcache = json.loads(CACHE_GW.read_text())
    net = json.loads(NET.read_text()); prev = json.loads(PREV.read_text())
    out = {'model': ('PRS s-family phi\'\'+(3-s)phi\'/tau-lap phi=-tau^(2s)(phi^2-1)(lam phi+e(tau)), a=tau, lam=2/(w_ref tau_ref^s)^2, '
                     'cubic bias e(tau)=(3/4) sigma0 tau^(1-s)/X for constant physical X=sigma/Delta V (times a C^1 ramp from tau_on); '
                     's=1 is the physical equation of wall_annihilation_gw, s=0 the PRS fixed-width equation of wall_network. '
                     'Pressure balance t_ann=K X, t=tau^2/2, predicts tau_ann=(2KX)^(1/2) for every s.'),
           'method': ('float32, dx=1, dt=0.2, tau_i=1, Gaussian initial field rms 0.1 cut at a quarter of Nyquist (wall_network.initial_field), '
                      'periodic box; network measured every unit of tau; runs stop once min(f,1-f)<0.002. Tensor runs: '
                      'u\'\'+2u\'/tau-lap u=16 pi tau^(1-s) d_i phi d_j phi, TT spectra every 4 units (wall_annihilation_gw.tt_spectra).'),
           'series_caches': {str(c.relative_to(ROOT)): hashlib.sha256(c.read_bytes()).hexdigest() for c in (CACHE_ANN, CACHE_GW)}}
    A_ref, rows = ann_rows(cache)
    out['A_ref_unbiased'] = {str(s): v for s, v in A_ref.items()}
    out['A_windows'] = {str(s): list(w) for s, w in A_WINDOW.items()}
    main0 = select(rows, s=0., N=320, w_ref=2., tau_on=4.)
    m05 = select(rows, s=.5, N=320); m1 = select(rows, s=1., N=320)
    ann = {'runs': rows, 'bias_over_barrier_cut': B_CUT, 'K_PRS_wall_network': K_PRS,
           'C_ann_times_A_wall_network': net['annihilation_factor']['K_equals_C_ann_times_A'],
           'previous_physical_192': {'p': prev['annihilation']['fit_false_1pct']['power_law_p'],
                                     'p_stderr': prev['annihilation']['fit_false_1pct']['power_law_p_stderr'],
                                     'K_offset': prev['annihilation']['fit_false_1pct']['offset_model']['K']}}
    for name, rr in (('s0', main0), ('s0.5', m05), ('s1', m1)):
        blk = {}
        for crit in ('tau_false_1pct', 'tau_false_10pct', 'tau_A_half'):
            blk[crit] = {'all': fit_block(rr, crit), 'asymptotic_subset': fit_block(rr, crit, B_CUT),
                         'seeds_all': seed_spread(rr, crit), 'seeds_asymptotic_subset': seed_spread(rr, crit, B_CUT)}
        blk['local_exponents_1pct'] = local_table(rr)
        blk['local_exponents_10pct'] = local_table(rr, 'tau_false_10pct')
        ann[name] = blk
    ann['controls_s0'] = controls_s0(rows, main0)
    ann['verdict_s0'] = verdict_s0(main0, ann['controls_s0'], A_ref.get(0.))
    out['annihilation'] = ann
    g = gw_analysis(gcache)
    out['gw'] = {'runs': g,
                 'summary_s0_peak_ge_3_box': gw_summary(g, 0., tmin=12.),
                 'summary_s0_peak_ge_5_box': gw_summary(g, 0., tmin=12., peak_over_box_min=5.),
                 'summary_s05_peak_ge_3_box': gw_summary(g, .5, tmin=30.),
                 'physical_s1_wall_gw_reference': json.loads(WALL_GW.read_text())['spectral_shape']}
    # box test: peak f/H at common tau across N (s=0)
    common = {}
    for r in g:
        if r['params']['s'] != 0.:
            continue
        for x in r['series']:
            common.setdefault(round(x['tau']), {})['N%d_seed%d' % (r['params']['N'], r['params']['seed'])] = {
                'peak_f_over_H': x['peak_f_over_H'], 'peak_over_box': x['peak_over_box'], 'eps_gw_kin': x['eps_gw_kin']}
    out['gw']['s0_peak_by_box_at_common_tau'] = {str(t): v for t, v in sorted(common.items()) if len(v) >= 3}
    out['scope'] = ('Float32 lattice, periodic boxes 320^3 (256^3 and 384^3 box controls; 192^3, 256^3 and 320^3 for GW). The s<1 runs use the PRS '
                    'width-growing (fat-wall) equations; the wall equation of motion is the physical one by construction, but the '
                    'wall profile and its scalar radiation are not. No backreaction, no thermal friction, not certified.')
    RECEIPT.write_text(json.dumps(_round(out), indent=1, sort_keys=True)+'\n')
    for name in ('s0', 's0.5', 's1'):
        b = ann[name]
        print(name, 'all', json.dumps(b['tau_false_1pct']['all']))
        print(name, 'asym', json.dumps(b['tau_false_1pct']['asymptotic_subset']))
        print(name, 'seeds', json.dumps(b['tau_false_1pct']['seeds_all']), json.dumps(b['tau_false_1pct']['seeds_asymptotic_subset']))
        print(name, '10pct', json.dumps(b['tau_false_10pct']['all']))
        print(name, 'Ahalf', json.dumps(b['tau_A_half']['all']))
        for x in b['local_exponents_1pct']:
            print('   local', json.dumps(x))
    print(json.dumps(ann['controls_s0']))
    print('A_ref', A_ref)
    for r in rows:
        p = r['params']
        print(p['s'], p['N'], p['w_ref'], p['tau_on'], p['seed'], p['X'], 'tau1=%.1f tau10=%.1f tauA=%.1f b/B=%.3f K=%.2f w=%.2f' % (
            r['tau_false_1pct'], r['tau_false_10pct'], r['tau_A_half'], r['bias_over_barrier_at_ann'], r['K_naive'], r['width_at_ann']))
    for r in g:
        print(r['params'])
        for x in r['series']:
            print('  tau=%.0f A=%.3f eps=%.3f/%.3f f/H=%.2f pk/box=%.1f IR=%.2f(%d) sup=%.2f(%d) sub=%.2f(%d) UV=%.2f' % (
                x['tau'], x['A'], x['eps_gw_kin'], x['eps_gw_avg'], x['peak_f_over_H'], x['peak_over_box'], x['IR_slope_all'], x['n_ir_bins'],
                x['IR_slope_superhorizon'], x['n_superhorizon_bins'], x['IR_slope_subhorizon'], x['n_subhorizon_ir_bins'], x['UV_slope']))
    for k in ('summary_s0_peak_ge_3_box', 'summary_s0_peak_ge_5_box', 'summary_s05_peak_ge_3_box'):
        print(k, json.dumps(out['gw'][k]))


if __name__ == '__main__':
    main()
