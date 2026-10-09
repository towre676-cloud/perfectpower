"""All-polarization vector widths, Goldstone equivalence, off-shell VV* and the
longitudinal-vector threshold of the 154.225 GeV wall mode.

Replay: OPENBLAS_NUM_THREADS=1 PYTHONPATH=python python python/develop_wall_mode_vector_widths.py
(about 40 minutes on one core). Writes receipts/flavor_cosmology/wall_mode_vector_widths.json.
"""
from pathlib import Path
import json
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall
from perfectpower.wall_gauge_channels import candidate_channel_solution
from perfectpower.wall_pair_decay import candidate_pair_data
from perfectpower import wall_mode_vector_widths as V

ROOT = Path(__file__).resolve().parents[1]
GPRIME = .36
G_PHYS = .65
ALPHA_S = .110          # declared alpha_s near the mode mass
FERMIONS = {            # declared Yukawa masses (GeV): low = running near 150 GeV, high = m(m) / pole-like
    'b': {'colors': 3, 'low': 2.75, 'high': 4.18},
    'c': {'colors': 3, 'low': 0.60, 'high': 1.27},
    'tau': {'colors': 1, 'low': 1.777, 'high': 1.777},
    'mu': {'colors': 1, 'low': 0.1057, 'high': 0.1057},
}


def log(tag, obj):print(tag, json.dumps(obj)[:400], flush=True)


def strip(r):return {k: v for k, v in r.items() if k not in ('outer_rows',)}


def main():
    import sys
    if '--quick' in sys.argv:   # smoke test only: coarse off-shell nodes, receipt not written to the repository
        full = V.offshell_pair_width
        V.offshell_pair_width = lambda *a, **k: full(*a, **{**k, 'outer': 3, 'inner': 2})
    model = WallModel(30000, .1, .025, 300000, 3000); bath = HiggsWall()
    sol = candidate_channel_solution(model, bath)
    prof = V.candidate_profile(sol)
    out = {'inputs': {'v_GeV': 30000, 'M_heavy_GeV': 300000, 'g_source_GeV': 3000, 'v_H_GeV': bath.v_GeV,
                      'lambda_H': bath.lam, 'portal_kappa': bath.portal, 'declared_gprime': GPRIME,
                      'physical_declared_g': G_PHYS, 'alpha_s': ALPHA_S, 'fermion_masses_GeV': FERMIONS,
                      'mode_mass_GeV': prof['M_GeV'], 'wall_scale_kv_GeV': prof['scale_GeV'],
                      'max_relative_Higgs_barrier_h2_over_h02_minus_1': prof['max_relative_barrier']}}
    out['exact_identities'] = V.exact_identities(); log('identities', len(out['exact_identities']))

    # 1. on-shell all-polarization pair widths
    gold = candidate_pair_data(sol, channel='global_Goldstone', momentum_nodes=193, spatial_nodes=2601, order=64)
    out['ungauged_Goldstone_reference_GeV'] = gold['width_GeV']
    out['coupling_scan'] = V.coupling_scan(prof, [.3, .4, .5, .6, G_PHYS], GPRIME)
    for r in out['coupling_scan']:log('scan', {'g': r['declared_g'], 'total': r['total_vector_pair_width_GeV']})
    controls = []
    for n, nx, order in [(97, 1301, 32), (193, 2601, 64), (289, 3901, 96)]:
        p = V.candidate_profile(sol, spatial_nodes=nx)
        for g in [.4, .6]:
            row = V.coupling_scan(p, [g], GPRIME, momentum_nodes=n, order=order)[0]
            controls.append({'momentum_nodes': n, 'spatial_nodes': nx, 'phase_space_order': order, **row})
            log('control', {'n': n, 'g': g, 'total': row['total_vector_pair_width_GeV']})
    out['resolution_controls'] = controls
    short = candidate_channel_solution(model, bath, length=18)
    out['domain_18_control'] = V.coupling_scan(V.candidate_profile(short), [.4, .6], GPRIME)
    fine = [c for c in controls if c['momentum_nodes'] == 289 and c['declared_g'] == .4][0]
    out['TE_reproduces_main'] = {'W_TE_GeV': fine['WW']['TE_GeV'], 'main_W_TE_GeV': 9.20148937628e-10,
                                 'Z_TE_GeV': fine['ZZ']['TE_GeV'], 'main_Z_TE_GeV': 8.44715462700e-10}
    out['threshold_scan_WW'] = V.threshold_scan(prof, [.1, .03, .01, .003, .001, .0003, .0001, .00003], order=96)
    log('threshold', out['threshold_scan_WW'][-1]['log_slopes'])

    # 2. Goldstone equivalence
    gs = [.2, .1, .05, .025, .0125, .00625, .003125]
    out['Goldstone_equivalence'] = V.goldstone_equivalence_scan(prof, [g*g for g in gs], gold['width_GeV'])
    log('equivalence', out['Goldstone_equivalence']['extrapolation'])

    # 3. physical coupling: closed on-shell pairs, off-shell VV*, fermions, gluons
    tree = V.declared_vector_widths(G_PHYS, GPRIME, bath.v_GeV)
    qcd = V.declared_vector_widths(G_PHYS, GPRIME, bath.v_GeV, alpha_s=ALPHA_S)
    out['declared_vector_widths'] = {'tree': tree, 'alpha_s_corrected': qcd}
    cW, cZ = G_PHYS**2, G_PHYS**2+GPRIME**2
    off = {'resolution': [], 'variants': []}
    for outer, inner, mn, order in [(8, 6, 97, 48), (12, 8, 97, 48), (16, 12, 97, 48), (12, 8, 145, 64)]:
        W = V.offshell_pair_width(prof, cW, tree['W_width_GeV'], identical=False, outer=outer, inner=inner, momentum_nodes=mn, order=order)
        Z = V.offshell_pair_width(prof, cZ, tree['Z_width_GeV'], identical=True, outer=outer, inner=inner, momentum_nodes=mn, order=order)
        off['resolution'].append({'WW_star': strip(W), 'ZZ_star': strip(Z), 'sum_GeV': W['width_GeV']+Z['width_GeV']})
        log('offshell res', {'outer': outer, 'inner': inner, 'mn': mn, 'W': W['width_GeV'], 'Z': Z['width_GeV']})
    variants = [('tree', True, 'physical', 1.), ('tree', True, 'physical', .25), ('tree', False, 'physical', 1.), ('tree', False, 'physical', .25),
                ('tree', True, 'rescaled', 1.), ('tree', False, 'rescaled', 1.), ('alpha_s_corrected', True, 'physical', 1.)]
    for widths_name, running, profile, mu_min in variants:
        widths = tree if widths_name == 'tree' else qcd
        W = V.offshell_pair_width(prof, cW, widths['W_width_GeV'], identical=False, running=running, profile=profile, mu_min_GeV=mu_min, outer=12, inner=8)
        Z = V.offshell_pair_width(prof, cZ, widths['Z_width_GeV'], identical=True, running=running, profile=profile, mu_min_GeV=mu_min, outer=12, inner=8)
        off['variants'].append({'widths': widths_name, 'running_width': running, 'leg_profile': profile, 'mu_min_GeV': mu_min,
                                'WW_star_GeV': W['width_GeV'], 'ZZ_star_GeV': Z['width_GeV'], 'sum_GeV': W['width_GeV']+Z['width_GeV'],
                                'WW_star_outer_rows': W['outer_rows'] if (widths_name, running, profile, mu_min) == ('tree', True, 'physical', 1.) else None})
        log('offshell var', {k: v for k, v in off['variants'][-1].items() if k != 'WW_star_outer_rows'})
    off['single_offshell_narrow_width_check'] = {
        'WW_star_GeV': V.single_offshell_width(prof, cW, tree['W_width_GeV'], identical=False, nodes=48)['width_GeV'],
        'ZZ_star_GeV': V.single_offshell_width(prof, cZ, tree['Z_width_GeV'], identical=True, nodes=48)['width_GeV'],
        'method': 'one leg exactly on shell, other leg running Breit-Wigner, factor 2; 48 Gauss nodes in sqrt(s)'}
    log('single', off['single_offshell_narrow_width_check'])
    out['offshell_VVstar'] = off
    ferm = {}
    for name, f in FERMIONS.items():
        ferm[name] = {lvl: V.fermion_pair_width(prof, f[lvl], f['colors'], order=128) for lvl in ('low', 'high')}
        ferm[name]['order_control_low'] = V.fermion_pair_width(prof, f['low'], f['colors'], order=96)['width_GeV']
    out['fermion_pairs'] = ferm
    glu = V.gluon_pair_width(prof, ALPHA_S, order=128)
    out['gluon_pair_LO'] = {**glu, 'order_control': V.gluon_pair_width(prof, ALPHA_S, order=96)['width_GeV']}
    log('fermions', {k: v['low']['width_GeV'] for k, v in ferm.items()}); log('gluons', glu['width_GeV'])

    base = [v for v in off['variants'] if v['widths'] == 'tree' and v['running_width'] and v['leg_profile'] == 'physical' and v['mu_min_GeV'] == 1.][0]
    # Fixed-width Breit-Wigner numerators (m Gamma instead of s Gamma/m) are kept as a diagnostic only:
    # with the 1/s longitudinal enhancement of a light virtual leg they are infrared-sensitive (mu_min dependence).
    sums = [v['sum_GeV'] for v in off['variants'] if v['running_width']]
    res = [r['sum_GeV'] for r in off['resolution']]
    f_low = sum(v['low']['width_GeV'] for v in ferm.values()); f_high = sum(v['high']['width_GeV'] for v in ferm.values())
    central = base['sum_GeV']+f_low+glu['width_GeV']
    gmin = min(sums+res)+f_low+glu['width_GeV']
    gmax = max(sums+res)+f_high+2*glu['width_GeV']
    out['lifetime_bracket'] = {
        'central_width_GeV': central, 'central_lifetime_s': V.HBAR_GEV_S/central,
        'width_bracket_GeV': [gmin, gmax], 'lifetime_bracket_s': [V.HBAR_GEV_S/gmax, V.HBAR_GEV_S/gmin],
        'central_composition_GeV': {'WW_star': base['WW_star_GeV'], 'ZZ_star': base['ZZ_star_GeV'],
                                    'fermion_pairs_running_masses': f_low, 'gluon_pair_LO': glu['width_GeV']},
        'bracket_construction': 'min/max of VV* over running-width variants (leg-profile prescription, tree/alpha_s widths, mu_min) and resolution; fixed-width BW excluded as infrared-sensitive; fermion masses low/high; gluons LO to 2xLO (NLO allowance).',
        'on_shell_WW_ZZ_open_at_physical_g': bool(out['coupling_scan'][-1]['WW']['open'] or out['coupling_scan'][-1]['ZZ']['open']),
        'omitted': 'gamma gamma, Z gamma and other loop-induced channels; electroweak and QCD loop corrections to the VV* and Yukawa vertices; top-mass form factor; interference; wall-induced fermion mass shifts.'}
    log('bracket', out['lifetime_bracket'])

    # 4. constrained longitudinal spectrum on the certified retuned wall
    mW = G_PHYS*bath.v_GeV/2; mZ = (cZ**.5)*bath.v_GeV/2
    pots = {name: V.longitudinal_potentials(prof, m) for name, m in [('W', mW), ('Z', mZ)]}
    spec = {'certified_statement': V.certified_threshold_statement(str(ROOT/'receipts/flavor_cosmology/wall_profile_intervals.json'),
                                                                   str(ROOT/'receipts/flavor_cosmology/wall_stability_certified.json')),
            'potential_extrema_GeV2': {n: {'longitudinal_excess_min': float(p['longitudinal_excess_GeV2'].min()),
                                           'longitudinal_excess_max': float(p['longitudinal_excess_GeV2'].max()),
                                           'transverse_excess_min': float(p['transverse_excess_GeV2'].min()),
                                           'transverse_excess_max': float(p['transverse_excess_GeV2'].max())} for n, p in pots.items()},
            'scattering_lengths': {f'g={g}': V.zero_energy_scattering_lengths(prof, g*bath.v_GeV/2) for g in [G_PHYS, .4, .1, .01]},
            'box_levels_W': [V.box_spectrum(prof, mW, radius_x=R, dx=dx) for R in [22., 88., 352., 1408.] for dx in [.0085, .00425]],
            'box_levels_Z': [V.box_spectrum(prof, mZ, radius_x=R, dx=.0085) for R in [22., 88., 352., 1408.]]}
    out['longitudinal_spectrum'] = spec
    log('spectrum', spec['certified_statement'])

    out['scope'] = ('Tree-level unitary-gauge distorted-wave Born widths on the fixed numerical wall (floating point, numerical controls, '
                    'no interval enclosures). On-shell widths at declared g<g_c; off-shell VV* by double Breit-Wigner convolution with declared '
                    'tree widths; Yukawa and heavy-top gluon channels with plane-wave fermions/gluons. Longitudinal spectrum: exact composition '
                    'of the retuned-wall Arb profile certificate with symbolic factorizations, plus numerical box/threshold controls.')
    out['not_claimed'] = ['loop-induced gamma gamma / Z gamma channels', 'NLO QCD or electroweak corrections', 'a Lean theorem',
                          'interval enclosure of any width', 'thermal or nonlinear real-time gauged evolution',
                          'the declared lambda=0.1 wall (only the retuned wall profile certificate is used)',
                          'experimentally matched couplings (g, gprime are declared benchmarks)']
    path = ROOT/'receipts/flavor_cosmology/wall_mode_vector_widths.json'
    if '--quick' in sys.argv:path = Path(sys.argv[sys.argv.index('--quick')+1])
    path.write_text(json.dumps(out, indent=1, sort_keys=True, default=float)+'\n')
    print('receipt', path, flush=True)


if __name__ == '__main__':
    main()
