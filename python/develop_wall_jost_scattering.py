"""Coupled-channel scattering, the open-channel shape resonance and its controls."""
from dataclasses import replace
from pathlib import Path
from math import sqrt
import hashlib, json
import numpy as np
from perfectpower.dimensionful_walls import WallModel, radiation_H
from perfectpower.wall_fluctuations import HiggsWall, solve_coupled_wall
from perfectpower import wall_jost_scattering as ws

ROOT = Path(__file__).resolve().parents[1]
EPS_LADDER = (1e4, 3e4, 1e5, 3e5)


def c(z):
    z = complex(z)
    return [z.real, z.imag]


def sector_tables(wall, energies, **kw):
    _, St = ws.s_matrix(wall, 'translation', energies, **kw)
    _, So = ws.s_matrix(wall, 'opposite', energies, **kw)
    rows = []
    for E, a, b in zip(energies, St, So):
        fl = ws.full_line(a['S'], b['S'])
        rows.append({'E_over_v2': float(E), 'open_channels': a['open_channels'],
                     'translation_phases': np.angle(np.diag(a['S'])).tolist(),
                     'opposite_phases': np.angle(np.diag(b['S'])).tolist(),
                     'reflection_probabilities': (abs(fl['reflection'])**2).tolist(),
                     'transmission_probabilities': (abs(fl['transmission'])**2).tolist(),
                     'sector_unitarity_defects': [a['unitarity_defect'], b['unitarity_defect']],
                     'full_line_unitarity_defect': fl['unitarity_defect']})
    return rows


def resonance(wall, *, spacing=.02, **kw):
    """Decoupled shape state (FEM and Jost), Feshbach self-energy and closed form."""
    state = ws.shape_bound_state(wall, spacing=spacing)
    Eb, hist = ws.find_pole(wall, 'opposite', state['E'], decouple=True, **kw)
    se = ws.higgs_green_self_energy(wall, state)
    an = ws.analytic_shape_width(wall)
    G = -2*se['Sigma'].imag
    return {'E_shape_FEM': state['E'], 'E_shape_Jost': c(Eb), 'Jost_iterations': len(hist),
            'Sigma': c(se['Sigma']), 'Gamma_E': G, 'golden_rule_Gamma_E': se['golden_rule_Gamma_E'],
            'standing_wave_overlap': se['standing_wave_overlap'],
            'wronskian_relative_spread': se['wronskian_relative_spread'],
            'closed_form_Gamma_E': an['Gamma_E'], 'closed_form_relative_difference': G/an['Gamma_E'] - 1,
            'physical': ws.physical_width(state['E'] + se['Sigma'].real, G, wall['model'].v_GeV)}, Eb, se


def main():
    source = ROOT/'receipts/flavor_cosmology/dimensionful_walls.json'
    old = json.loads(source.read_text())
    model = replace(WallModel(**old['declared_model_inputs']), bias_h0_GeV3=0., bias_onset_GeV=0.)
    bi = old['declared_bath_completion']
    bath = HiggsWall(bi['portal_kappa'], bi['Higgs_lambda'], bi['Higgs_v_GeV'])
    wall = solve_coupled_wall(model, bath)
    mu, V = ws.vacuum_channels(wall)
    out = {'input_dimensionful_receipt_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
           'declared_model': model.__dict__, 'declared_Higgs': bath.__dict__,
           'units': 'rho=v z; E=omega^2/v^2; Hessian in units of v^2; v=%r GeV' % model.v_GeV,
           'vacuum_thresholds_over_v2': mu.tolist(), 'vacuum_eigenchannels_columns': V.tolist(),
           'half_box_rho': wall['L']}

    # 1. Decoupled Poschl-Teller and free-Higgs limits.
    pt = solve_coupled_wall(replace(model, current_g_GeV=0.), HiggsWall(0., bath.lam, bath.v_GeV))
    k = pt['k']
    E = np.array([.25, .5, 1., 3.])
    _, St = ws.s_matrix(pt, 'translation', E)
    _, So = ws.s_matrix(pt, 'opposite', E)
    rows = []
    for e, a, b in zip(E, St, So):
        fl = ws.full_line(a['S'], b['S'])
        q = sqrt(e - 4*k*k)
        tPT = (q + 1j*k)*(q + 2j*k)/((q - 1j*k)*(q - 2j*k))
        rows.append({'E_over_v2': e, 'source_transmission_error': abs(-fl['transmission'][1, 1] - tPT),
                     'source_reflection_probability': abs(fl['reflection'][1, 1])**2,
                     'Higgs_transmission_error': abs(fl['transmission'][0, 0] - 1),
                     'full_line_unitarity_defect': fl['unitarity_defect']})
    z0 = ws.find_pole(pt, 'translation', 1e-6)[0]
    z1 = ws.find_pole(pt, 'opposite', .149)[0]
    out['Poschl_Teller_limit'] = {
        'inputs': 'g=0 and kappa=0: source is the exact l=2 Poschl-Teller kink, Higgs is free',
        'scattering': rows, 'translation_pole': c(z0), 'shape_pole': c(z1),
        'shape_pole_minus_3k2': complex(z1).real - 3*k*k,
        'convention': 'Left-hand channels use D e_j, so the source transmission is -t_PT with t_PT=(q+ik)(q+2ik)/((q-ik)(q-2ik)).'}

    # 2. Zero portal with the mediator retained: the Higgs channel is exactly free.
    zp = solve_coupled_wall(model, HiggsWall(0., bath.lam, bath.v_GeV))
    zr = sector_tables(zp, np.array([1e-3, .1, .3]))
    out['zero_portal_limit'] = {'tables': zr,
                                'maximum_Higgs_phase_from_free': max(max(abs(r['translation_phases'][0]), np.pi - abs(r['opposite_phases'][0])) for r in zr),
                                'shape_state_is_embedded_but_decoupled': True}

    # 3. Physical wall: translation pole in the continuum and the shape resonance.
    zt = [ws.find_pole(wall, 'translation', 1e-6, h_core=h)[0] for h in (.004, .002)]
    out['translation_zero_mode_pole'] = {'h_core_004': c(zt[0]), 'h_core_002': c(zt[1]),
                                         'below_Higgs_threshold': bool(abs(zt[1]) < mu[0])}
    res, Eb, se = resonance(wall)
    out['shape_resonance'] = res
    ladder = []
    for eps in EPS_LADDER:
        Ep, hist = ws.find_pole(wall, 'opposite', Eb.real + eps**2*se['Sigma'], coupling_scale=eps)
        ladder.append({'coupling_scale': eps, 'pole': c(Ep), 'iterations': len(hist),
                       'reduced_shift': c((Ep - Eb)/eps**2),
                       'relative_difference_from_Sigma': abs((Ep - Eb)/eps**2 - se['Sigma'])/abs(se['Sigma'])})
    out['coupling_ladder'] = {
        'meaning': 'coupling_scale multiplies only the phi-h entries of the fluctuation operator; the background wall is unchanged. Second-order theory predicts (E_pole-E_shape)/scale^2=Sigma+O(scale^2).',
        'rows': ladder}
    d = ws.jost_function(wall, 'opposite', [Eb.real + se['Sigma'], Eb.real + se['Sigma'].real, Eb.real + 1e-12])[1]
    out['physical_direct_pole_check'] = {
        'abs_F_at_predicted_pole': float(abs(d[0])), 'abs_F_at_real_axis_projection': float(abs(d[1])),
        'abs_F_at_1e-12_offset': float(abs(d[2])),
        'resolved': False,
        'meaning': 'At the physical coupling the width is about 1e-17 of E_r, at the floating-point floor of the Jost function. The direct pole is consistent with, but not independent of, the second-order result; the ladder above is the independent numerical confirmation.'}

    # 4. Real-axis Breit-Wigner check on two ladder couplings.
    bw = []
    x = np.linspace(-6, 6, 49)
    for row in ladder[1:3]:
        eps = row['coupling_scale']; Ep = complex(*row['pole']); G = -2*Ep.imag
        Es = Ep.real + x*G
        S = np.array([s['S'][0, 0] for s in ws.s_matrix(wall, 'opposite', Es, coupling_scale=eps)[1]])
        bg = np.array([s['S'][0, 0] for s in ws.s_matrix(wall, 'opposite', Es, coupling_scale=eps, decouple=True)[1]])
        model_S = bg*(Es - Ep.conjugate())/(Es - Ep)
        bw.append({'coupling_scale': eps, 'x_over_Gamma': x.tolist(), 'phase': np.unwrap(np.angle(S/bg)).tolist(),
                   'max_Breit_Wigner_deviation': float(np.max(abs(S - model_S))),
                   'max_unitarity_defect': float(np.max(abs(abs(S) - 1))),
                   'phase_advance_over_window': float(np.unwrap(np.angle(S/bg))[-1] - np.unwrap(np.angle(S/bg))[0])})
    out['real_axis_Breit_Wigner'] = bw

    # 5. Physical S-matrix tables and full-line reflection.
    grid = np.r_[np.geomspace(2e-5, .19, 22), np.geomspace(.205, 50, 18)]
    out['physical_scattering'] = sector_tables(wall, grid)
    theta = V[0, 0]  # phi component of the Higgs-like eigenchannel
    out['sudden_rotation_check'] = {
        'Higgs_channel_phi_component': theta, 'predicted_high_energy_conversion': 4*theta**2,
        'computed_conversion_at_highest_E': out['physical_scattering'][-1]['transmission_probabilities'][0][1],
        'meaning': 'The eigenchannels at the two vacua are e_j and D e_j, so the mixing angle flips sign across the wall. A thin (sudden) wall converts with probability 4 theta^2.'}

    # 6. Error controls.
    controls = {}
    probe = np.array([1e-4, .1, .3, 5.])
    base = sector_tables(wall, probe)
    def diff(rows):
        return max(abs(np.exp(1j*a) - np.exp(1j*b)) for r0, r1 in zip(base, rows)
                   for k_ in ('translation_phases', 'opposite_phases') for a, b in zip(r0[k_], r1[k_]))
    for name, kw in [('h_core_half', {'h_core': .002}), ('h_tail_half', {'h_tail': .1}),
                     ('R_half', {'R': wall['L']/2}), ('R_three_quarter', {'R': .75*wall['L']}),
                     ('Johnson_tail_h_02', {'tail': 'johnson', 'h_tail': .02})]:
        controls[name] = diff(sector_tables(wall, probe, **kw))
    box = {}
    for lf in (8., 16.):
        w2 = solve_coupled_wall(model, bath, length_factor=lf)
        r2 = resonance(w2)[0]
        box[str(lf)] = {'half_box_rho': w2['L'], 'Gamma_E': r2['Gamma_E'], 'E_shape_FEM': r2['E_shape_FEM'],
                        'max_phase_difference': diff(sector_tables(w2, probe))}
    fine = resonance(wall, spacing=.01, h_core=.002)[0]
    out['error_controls'] = {'max_phase_change': controls, 'box_length_factors': box,
                             'FEM_spacing_01_Gamma_E': fine['Gamma_E'], 'FEM_spacing_01_E_shape': fine['E_shape_FEM'],
                             'FEM_spacing_01_Jost_E_shape': fine['E_shape_Jost'],
                             'note': 'Pure Johnson propagation over the 2870-unit Higgs tail is retained only as a contrast; its accumulated O(h^4) phase error is why the exact-reference tail is used.'}

    # 7. Sensitivity to declared couplings (second-order Feshbach, wall re-solved each time).
    sens = []
    for label, m2, b2 in [('kappa=1e-8', model, HiggsWall(1e-8, bath.lam, bath.v_GeV)),
                          ('kappa=3e-8', model, HiggsWall(3e-8, bath.lam, bath.v_GeV)),
                          ('kappa=3e-7', model, HiggsWall(3e-7, bath.lam, bath.v_GeV)),
                          ('kappa=1e-6', model, HiggsWall(1e-6, bath.lam, bath.v_GeV)),
                          ('lambda_H=0.10', model, HiggsWall(bath.portal, .10, bath.v_GeV)),
                          ('lambda_H=0.20', model, HiggsWall(bath.portal, .20, bath.v_GeV)),
                          ('g=0', replace(model, current_g_GeV=0.), bath),
                          ('g=30000', replace(model, current_g_GeV=30000.), bath)]:
        w2 = solve_coupled_wall(m2, b2)
        r2 = resonance(w2)[0]
        sens.append({'variation': label, 'Gamma_E': r2['Gamma_E'], 'Gamma_GeV': r2['physical']['Gamma_GeV'],
                     'closed_form_relative_difference': r2['closed_form_relative_difference'],
                     'central_Higgs_GeV': w2['report']['central_Higgs_GeV'],
                     'Gamma_over_kappa2': r2['Gamma_E']/b2.portal**2})
    out['sensitivity'] = sens
    rs = {}
    for label, m2, b2, E0 in [('Higgs_kappa_half', model, HiggsWall(bath.portal/2, bath.lam, bath.v_GeV), 1e-3),
                              ('source_g_half', replace(model, current_g_GeV=1500.), bath, .3)]:
        w2 = solve_coupled_wall(m2, b2)
        r2 = sector_tables(w2, np.array([E0]))[0]
        r1 = sector_tables(wall, np.array([E0]))[0]
        j = 0 if E0 < .2 else 1
        rs[label] = {'E_over_v2': E0, 'reflection_ratio': r2['reflection_probabilities'][j][j]/r1['reflection_probabilities'][j][j]}
    out['reflection_scaling'] = rs

    # 8. Conditional comparison with radiation-era expansion (input g*).
    G = res['physical']['Gamma_GeV']
    Teq = sqrt(G*2.435e18/sqrt(np.pi**2*106.75/90))
    out['expansion_comparison'] = {'gstar': 106.75, 'T_where_Gamma_equals_H_GeV': Teq,
                                   'H_at_T_eq_GeV': radiation_H(Teq, 106.75),
                                   'scope': 'Zero-temperature vacuum width compared with a radiation-era H(T) for an input g*. Plasma damping, thermal masses, nonlinear radiation and Higgs-bath occupation are not included.'}

    out['conclusions'] = {
        'shape_mode_is_open_channel_resonance': True,
        'pole_sheet': 'Higgs channel continued from q>0 to Im q<0; source and mediator channels decaying (Im q>0)',
        'translation_mode_is_continuum_bound_state': True,
        'kink_reflectionless_property_broken_by_mediator': True,
        'certified': False,
        'nonlinear_shape_radiation_included': False,
        'thermal_or_network_prediction_changed': False}
    out['scope'] = ('Linear coupled-channel scattering of the supplied unbiased spectator wall: radial Higgs, source and Gaussian mediator, '
                    'all three channels retained. Floating-point numerics with step, matching-radius, box and mesh controls, a '
                    'closed-form leading width and an operator-level coupling ladder. Not a rigorous enclosure, not a continuum '
                    'stability theorem, and no angular Higgs, gauge, fermion, thermal-plasma, nonlinear (two-quantum) or '
                    'network dynamics.')
    path = ROOT/'receipts/flavor_cosmology/wall_jost_scattering.json'
    path.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'E_shape': res['E_shape_FEM'], 'Sigma': res['Sigma'], 'Gamma_GeV': res['physical']['Gamma_GeV'],
                      'lifetime_s': res['physical']['lifetime_s'],
                      'closed_form_relative_difference': res['closed_form_relative_difference'],
                      'ladder_relative_differences': [r['relative_difference_from_Sigma'] for r in ladder],
                      'translation_pole': out['translation_zero_mode_pole']['h_core_002'],
                      'controls': controls}, indent=2))


if __name__ == '__main__':
    main()
