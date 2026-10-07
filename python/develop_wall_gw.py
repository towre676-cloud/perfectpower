"""Gravitational waves from the physical wall network on the lattice."""
from pathlib import Path
from multiprocessing import Pool
import hashlib, json, os, sys
import numpy as np
from perfectpower import wall_network as wn
from perfectpower.dimensionful_walls import WallModel, annihilation, gw_estimate

ROOT = Path(__file__).resolve().parents[1]
CACHE = ROOT/'receipts/flavor_cosmology/wall_gw_series.json'
RUNS = [dict(N=256, seed=0), dict(N=256, seed=1), dict(N=192, seed=0), dict(N=256, seed=0, w_final=3.)]
LATE = .6  # fraction of tau_f after which the efficiency is averaged


def run(kw):
    os.environ['OPENBLAS_NUM_THREADS'] = '1'
    return kw, wn.evolve_physical_gw(**kw, measure_every=6.)


def simulate():
    with Pool(4) as pool:
        res = pool.map(run, RUNS)
    CACHE.write_text(json.dumps([{'params': k, **r} for k, r in res], sort_keys=True)+'\n')


def spectrum_shape(k, s, tau):
    """Peak k_p tau/(2 pi) (cyclic frequency over aH) and log slopes on either side of the peak."""
    k, s = np.asarray(k), np.asarray(s)
    good = s > 0
    k, s = k[good], s[good]
    j = int(np.argmax(s))
    x = k*tau/(2*np.pi)
    ir = (x < x[j]/1.5) & (x > x[j]/6)
    uv = (x > x[j]*1.5) & (k < .5*np.pi)  # stay below a quarter of the lattice cutoff
    fit = lambda m: float(np.polyfit(np.log(x[m]), np.log(s[m]), 1)[0]) if m.sum() >= 3 else float('nan')
    return {'peak_f_over_H': float(x[j]), 'IR_slope': fit(ir), 'UV_slope': fit(uv)}


def main():
    if '--simulate' in sys.argv or not CACHE.exists():
        simulate()
    runs = json.loads(CACHE.read_text())
    out = {'method': ('Physical radiation-era walls: phi\'\'+2phi\'/tau-lap phi=-tau^2 lam phi(phi^2-1), comoving width shrinking '
                      'to w_final at tau_f=N/2; tensor modes u_ij\'\'+2u_ij\'/tau-lap u_ij=16 pi G d_i phi d_j phi '
                      '(Garcia-Bellido, Figueroa and Sastre), transverse-traceless projection in Fourier space; '
                      'rho_gw=<h\'h\'>/(32 pi G a^2), eps_gw=rho_gw/(G A^2 sigma^2); tau_i=10, dt=0.2, float32.'),
           'series_cache_sha256': hashlib.sha256(CACHE.read_bytes()).hexdigest()}
    rows = []
    for r in runs:
        tau_f = r['rows'][-1]['tau']
        series = []
        for x in r['rows']:
            k = np.asarray(x['k']); sp = np.asarray(x['drho_dlnk'])
            j = int(np.argmax(sp))
            series.append({'tau': x['tau'], 'eps_gw': x['eps_gw'], 'A': x['A'],
                           'peak_f_over_H': float(k[j]*x['tau']/(2*np.pi)), 'peak_bin': j,
                           'box_f_over_H': float(k[0]*x['tau']/(2*np.pi))})
        formed = [x for x in series if x['A'] < 1.2 and x['eps_gw'] > .05]
        late = [x for x in series if x['tau'] >= LATE*tau_f]
        last = r['rows'][-1]
        shape = spectrum_shape(last['k'], last['drho_dlnk'], last['tau'])
        rows.append({'params': r['params'], 'lam': r['lam'], 'final_width': last['width_comoving'],
                     'eps_gw_late_mean': float(np.mean([x['eps_gw'] for x in late])),
                     'eps_gw_max_after_formation': float(max(x['eps_gw'] for x in formed)),
                     'eps_gw_final': last['eps_gw'], 'A_late_mean': float(np.mean([x['A'] for x in late])),
                     'UV_slope_final': shape['UV_slope'],
                     'peak_resolved_times': [x for x in formed if x['peak_bin'] >= 2],
                     'peak_box_limited_at_end': series[-1]['peak_bin'] <= 1, 'series': series})
    out['runs'] = rows
    main_runs = rows[:2]
    eps_lo = float(min(r['eps_gw_final'] for r in rows))
    eps_hi = float(max(r['eps_gw_max_after_formation'] for r in rows))
    eps = float(np.mean([r['eps_gw_late_mean'] for r in main_runs]))
    resolved = [x['peak_f_over_H'] for r in main_runs for x in r['peak_resolved_times']]
    uv = float(np.mean([r['UV_slope_final'] for r in main_runs]))
    out['efficiency'] = {'eps_gw_late_mean_main': eps, 'bracket': [eps_lo, eps_hi],
                         'A_physical_late': float(np.mean([r['A_late_mean'] for r in main_runs])),
                         'note': 'eps_gw rises after network formation and then declines; it does not plateau within these boxes, so the bracket spans the end values to the post-formation maximum.'}
    out['spectral_shape'] = {'peak_f_over_H_resolved_range': [min(resolved), max(resolved)],
                             'peak_box_limited_at_end': all(r['peak_box_limited_at_end'] for r in main_runs),
                             'UV_slope': uv, 'UV_slopes_all_runs': [r['UV_slope_final'] for r in rows],
                             'IR_slope': None,
                             'note': 'The peak stays at a fixed comoving wavenumber while it is resolved (f/H grows from about 0.5 to 1) and reaches the box scale by the end, so only f_peak/H <~ 0.5-1 is established; the IR slope is not measurable in these boxes.'}
    shape = {'peak_f_over_H': float(np.median(resolved)), 'UV_slope': uv}

    # Update the conditional template with lattice A, C_ann (wall_network.json) and these GW numbers.
    net = json.loads((ROOT/'receipts/flavor_cosmology/wall_network.json').read_text())
    old = json.loads((ROOT/'receipts/flavor_cosmology/dimensionful_walls.json').read_text())
    model = WallModel(**old['declared_model_inputs'])
    sigma = json.loads((ROOT/'receipts/flavor_cosmology/wall_stability.json').read_text())['three_field_wall']['tension_GeV3']
    A = net['area_parameter']['A']; C = float(np.median(net['annihilation_factor']['C_ann_false_1pct_values']))
    a = annihilation(model, sigma, area=A, annihilation_factor=C)
    def template(e, x):
        return gw_estimate(sigma, a['H_GeV'], area=A, efficiency=e, peak_frequency_in_H=x,
                           middle_break=10., middle_slope=uv, uv_slope=uv, frequencies=np.array([1e-9]))
    g = template(eps, shape['peak_f_over_H'])
    corners = [{'efficiency': e, 'peak_f_over_H': x, 'peak_frequency_Hz': template(e, x)['peak_frequency_Hz'],
                'peak_Omega_h2': template(e, x)['peak_Omega_h2']}
               for e in out['efficiency']['bracket'] for x in out['spectral_shape']['peak_f_over_H_resolved_range']]
    d0 = annihilation(model, sigma, area=.8, annihilation_factor=3.)
    g0 = gw_estimate(sigma, d0['H_GeV'], area=.8, frequencies=np.array([1e-9]))
    out['declared_cosmology_update'] = {
        'declared': {'A': .8, 'C_ann': 3., 'efficiency': .7, 'peak_f_over_H': 1., 'UV_slope': -1.,
                     'T_ann_GeV': d0['temperature_GeV'], 'peak_frequency_Hz': g0['peak_frequency_Hz'], 'peak_Omega_h2': g0['peak_Omega_h2'],
                     'integrated_Omega_h2': g0['integrated_Omega_h2']},
        'lattice': {'A': A, 'C_ann': C, 'efficiency': eps, 'peak_f_over_H': shape['peak_f_over_H'], 'UV_slope': uv,
                    'T_ann_GeV': a['temperature_GeV'], 'peak_frequency_Hz': g['peak_frequency_Hz'], 'peak_Omega_h2': g['peak_Omega_h2'],
                    'integrated_Omega_h2': g['integrated_Omega_h2']},
        'bracket_corners': corners,
        'scope': 'All network and GW template inputs now come from lattice runs of this potential; the bias and emission epoch still follow the classical pressure-balance estimate, the IR slope is the causal k^3 template value, the peak position is only bounded by the box (resolved range used), and the spectrum is computed before annihilation.'}
    out['scope'] = ('Linear tensor modes on a periodic 3D lattice of the phi^4 wall network (the walls of the supplied model to 1e-6), '
                    'scaling regime only; box sizes 192^3 and 256^3, two seeds, two final widths. No annihilation-phase GW, no '
                    'backreaction, floating point.')
    path = ROOT/'receipts/flavor_cosmology/wall_gw.json'
    path.write_text(json.dumps(out, indent=1, sort_keys=True)+'\n')
    for r in rows:
        print(r['params'], 'eps late', r['eps_gw_late_mean'], 'max', r['eps_gw_max_after_formation'], 'final', r['eps_gw_final'],
              'A', r['A_late_mean'], 'UV', r['UV_slope_final'], 'boxlimited', r['peak_box_limited_at_end'])
    print(json.dumps(out['efficiency']), json.dumps(out['spectral_shape']))
    print(json.dumps(out['declared_cosmology_update'], indent=1))


if __name__ == '__main__':
    main()
