"""Lattice calibration of the wall-network area parameter and annihilation factor."""
from pathlib import Path
from multiprocessing import Pool
from dataclasses import replace
import hashlib, json, os
import numpy as np
from perfectpower import wall_network as wn
from perfectpower.dimensionful_walls import WallModel, annihilation, gw_estimate

ROOT = Path(__file__).resolve().parents[1]
UNBIASED = [dict(N=256, seed=s, lam=.5) for s in (0, 1, 2)] + [dict(N=256, seed=0, lam=.25), dict(N=128, seed=0, lam=.5),
                                                              dict(N=384, seed=0, lam=.5)]
BIASED = [dict(N=256, seed=0, lam=.5, eps1=e) for e in (1.5e-4, 3e-4, 6e-4, 1.2e-3)]
PLATEAU_FROM = 30.


def run(kw):
    os.environ['OPENBLAS_NUM_THREADS'] = '1'
    r = wn.evolve(**kw)
    keep = slice(None, None, 2)  # every 10th step
    return kw, {k: r[k][keep].tolist() for k in ('tau', 'A', 'false_fraction')}


def simulate():
    """Expensive stage (about 50 minutes on 4 cores): writes the raw series cache."""
    with Pool(4) as pool:
        results = pool.map(run, UNBIASED + BIASED)
    cache = {'unbiased': [{'params': k, 'series': r} for k, r in results[:len(UNBIASED)]],
             'biased': [{'params': k, 'series': r} for k, r in results[len(UNBIASED):]]}
    (ROOT/'receipts/flavor_cosmology/wall_network_series.json').write_text(json.dumps(cache, sort_keys=True)+'\n')


def main():
    import sys
    cache_path = ROOT/'receipts/flavor_cosmology/wall_network_series.json'
    if '--simulate' in sys.argv or not cache_path.exists():
        simulate()
    cache = json.loads(cache_path.read_text())
    results = [(x['params'], x['series']) for x in cache['unbiased'] + cache['biased']]
    out = {'method': 'PRS alpha=3 beta=0, a=tau, dx=1, dt=0.2, tau_i=1 to N/2; Gaussian initial field of rms 0.1 with modes above a quarter of the Nyquist frequency removed; float32; series recorded every 10 steps',
           'lattice_kink_check': {str(l): wn.lattice_kink_check(lam=l) for l in (.5, .25)},
           'plateau_from_tau': PLATEAU_FROM}
    runs = []
    for kw, r in results[:len(UNBIASED)]:
        tau, A = np.array(r['tau']), np.array(r['A'])
        mean, sd, slope = wn.fit_plateau(tau, A, PLATEAU_FROM)
        runs.append({'params': kw, 'A_mean': mean, 'A_std_in_time': sd, 'dlnA_dlntau': slope,
                     'A_final': float(A[-1]), 'tau_final': float(tau[-1]), 'series': r})
    out['unbiased'] = [{k: v for k, v in r.items() if k != 'series'} for r in runs]
    main3 = [r['A_mean'] for r in runs[:3]]
    A_hat = float(np.mean(main3))
    A_stat = float(np.std(main3, ddof=1)/np.sqrt(3))
    A_sys = float(max(abs(runs[3]['A_mean'] - runs[0]['A_mean']), abs(runs[5]['A_mean'] - runs[0]['A_mean'])))
    A_late = [r['A_final'] for r in runs]
    out['area_parameter'] = {'A': A_hat, 'statistical': A_stat, 'resolution_and_box_systematic': A_sys,
                             'scaling_slopes': [r['dlnA_dlntau'] for r in runs],
                             'A_final_range': [min(A_late), max(A_late)],
                             'note': 'A is the plateau mean over tau>=30; it still drifts upward (dlnA/dlntau 0.07-0.18) and reaches 0.97 at tau=192 in the largest box, so the scaling value is uncertain at the +20 percent level.'}
    bias = []
    for kw, r in results[len(UNBIASED):]:
        res = {k: np.array(v) for k, v in r.items()}
        t_half, t_ff = wn.annihilation_time(res, A_hat)
        bias.append({'params': kw, 'tau_A_half': t_half, 'tau_false_below_1pct': t_ff,
                     'C_ann_A_half': wn.C_ann(t_half, kw['eps1'], kw['lam'], A_hat),
                     'C_ann_false_1pct': wn.C_ann(t_ff, kw['eps1'], kw['lam'], A_hat),
                     'bias_over_barrier_at_A_half': kw['eps1']*t_half/(kw['lam']/4), 'series': r})
    out['biased'] = [{k: v for k, v in b.items() if k != 'series'} for b in bias]
    out['series_cache'] = {'path': 'receipts/flavor_cosmology/wall_network_series.json',
                           'sha256': hashlib.sha256(cache_path.read_bytes()).hexdigest()}
    Cs = [b['C_ann_false_1pct'] for b in bias if np.isfinite(b['C_ann_false_1pct'])]
    Ch = [b['C_ann_A_half'] for b in bias if np.isfinite(b['C_ann_A_half'])]
    out['annihilation_factor'] = {'C_ann_false_1pct_values': Cs, 'C_ann_range': [min(Cs), max(Cs)],
                                  'C_ann_A_half_values': Ch,
                                  'definition': 't_ann=C_ann*A*sigma/DeltaV; primary t_ann where the false-vacuum volume fraction first drops below 1 percent, secondary where A falls back to half its scaling value'}

    # Propagate to the declared conditional cosmology.
    old = json.loads((ROOT/'receipts/flavor_cosmology/dimensionful_walls.json').read_text())
    model = WallModel(**old['declared_model_inputs'])
    sigma = json.loads((ROOT/'receipts/flavor_cosmology/wall_stability.json').read_text())['three_field_wall']['tension_GeV3']
    decl = annihilation(model, sigma, area=.8, annihilation_factor=3.)
    prop = []
    # The lattice measures K=C_ann*A=t_ann DeltaV/sigma; a different A at fixed K rescales C_ann.
    K = float(np.median(Cs))*A_hat
    out['annihilation_factor']['K_equals_C_ann_times_A'] = K
    for Aa, C in [(A_hat, min(Cs)), (A_hat, float(np.median(Cs))), (A_hat, max(Cs)), (max(A_late), K/max(A_late))]:
        a = annihilation(model, sigma, area=Aa, annihilation_factor=C)
        g = gw_estimate(sigma, a['H_GeV'], area=Aa, frequencies=np.array([1e-9]))
        g0 = gw_estimate(sigma, decl['H_GeV'], area=.8, frequencies=np.array([1e-9]))
        prop.append({'A': Aa, 'C_ann': C, 'T_ann_GeV': a['temperature_GeV'], 'T_ann_over_declared': a['temperature_GeV']/decl['temperature_GeV'],
                     'peak_frequency_Hz': g['peak_frequency_Hz'], 'peak_Omega_h2': g['peak_Omega_h2'],
                     'peak_Omega_ratio_to_declared': g['peak_Omega_h2']/g0['peak_Omega_h2']})
    out['declared_cosmology_update'] = {'declared': {'A': .8, 'C_ann': 3., 'T_ann_GeV': decl['temperature_GeV']},
                                        'calibrated': prop,
                                        'scope': 'Same classical pressure-balance and GW template as the earlier conditional estimate, with A and C_ann replaced by this lattice calibration. Efficiency, g* and spectral shape remain supplied inputs.'}
    out['scope'] = ('PRS-modified phi^4 network in a periodic box (bias grown as eps1*tau to represent constant physical Delta V). '
                    'Walls of the supplied model are phi^4 kinks to 1e-6. The physical bias is 25 orders too small to simulate, so '
                    'C_ann is measured at small but finite bias/barrier ratios and its trend is reported. No GW extraction, '
                    'no full (non-PRS) wall thinning, and A, C_ann carry the stated statistical and systematic spreads.')
    path = ROOT/'receipts/flavor_cosmology/wall_network.json'
    path.write_text(json.dumps(out, indent=1, sort_keys=True)+'\n')
    print(json.dumps({k: out[k] for k in ('area_parameter', 'annihilation_factor')}, indent=1))
    for r in runs: print(r['params'], r['A_mean'], r['A_std_in_time'], r['dlnA_dlntau'])
    for b in bias: print(b['params']['eps1'], b['tau_A_half'], b['tau_false_below_1pct'], b['C_ann_A_half'], b['C_ann_false_1pct'], b['bias_over_barrier_at_A_half'])
    print(json.dumps(out['declared_cosmology_update'], indent=1))


if __name__ == '__main__':
    main()
