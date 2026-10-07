"""Nonlinear second-harmonic radiation of the wall shape mode and its crossover."""
from dataclasses import replace
from pathlib import Path
from math import sqrt, pi
import hashlib, json
import numpy as np
from perfectpower.dimensionful_walls import WallModel, HBAR_GEV_S
from perfectpower.wall_fluctuations import HiggsWall, solve_coupled_wall, potential_and_hessian
from perfectpower import wall_scattering as ws
from perfectpower import wall_shape_radiation as sr

ROOT = Path(__file__).resolve().parents[1]


def summary(r):
    return {k: r[k] for k in ('Omega2', 'open_channels', 'channel_power', 'P1', 'Gamma_NL_over_A2')}


def main():
    source = ROOT/'receipts/flavor_cosmology/dimensionful_walls.json'
    scat = ROOT/'receipts/flavor_cosmology/wall_scattering.json'
    old = json.loads(source.read_text())
    lin = json.loads(scat.read_text())
    model = replace(WallModel(**old['declared_model_inputs']), bias_h0_GeV3=0., bias_onset_GeV=0.)
    bi = old['declared_bath_completion']
    bath = HiggsWall(bi['portal_kappa'], bi['Higgs_lambda'], bi['Higgs_v_GeV'])
    v = model.v_GeV
    wall = solve_coupled_wall(model, bath)
    state = ws.shape_bound_state(wall)
    out = {'input_receipts_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in (source, scat)},
           'declared_model': model.__dict__, 'declared_Higgs': bath.__dict__,
           'units': 'rho=v z, t in units of 1/v, eta=A psi cos(omega t) with psi normalised on the full line'}

    # Cubic vertex against central differences of the published Hessian.
    z = np.array([.3, -.002, .01]); e = 1e-6
    fd = np.array([(potential_and_hessian(model, bath, *(z + e*np.eye(3)[i]))[1]
                    - potential_and_hessian(model, bath, *(z - e*np.eye(3)[i]))[1])/(2*e) for i in range(3)])
    saved = sr._profile
    sr._profile = lambda w_, rho: z[:, None]*np.ones((1, np.size(rho)))
    T = sr.cubic_vertex(wall, [0.])[0]
    sr._profile = saved
    out['cubic_vertex_check'] = {'max_abs_difference_from_finite_difference': float(np.max(abs(T - fd))),
                                 'fully_symmetric': bool(np.allclose(T, T.transpose(1, 0, 2)) and np.allclose(T, T.transpose(0, 2, 1)))}

    base = sr.second_harmonic(wall, state)
    out['physical_second_harmonic'] = summary(base)
    out['controls'] = {'spacing_01': sr.second_harmonic(wall, state, spacing=.01)['P1'],
                       'R_220': sr.second_harmonic(wall, state, R=220.)['P1'],
                       'state_spacing_01': sr.second_harmonic(wall, ws.shape_bound_state(wall, spacing=.01))['P1']}
    pt = solve_coupled_wall(replace(model, current_g_GeV=0.), HiggsWall(0., bath.lam, bath.v_GeV))
    kink = sr.second_harmonic(pt, ws.shape_bound_state(pt))
    cf = sr.kink_closed_form(model.lam)
    out['pure_kink'] = {'FEM': summary(kink), 'closed_form': cf,
                        'relative_difference': kink['P1']/cf['P1'] - 1,
                        'mediator_and_portal_relative_effect': base['P1']/kink['P1'] - 1}
    w2 = solve_coupled_wall(model, HiggsWall(2*bath.portal, bath.lam, bath.v_GeV))
    hp = sr.second_harmonic(w2, ws.shape_bound_state(w2))['channel_power'][0]
    out['Higgs_channel_power_ratio_at_double_portal'] = hp/base['channel_power'][0]

    # Independent nonlinear time-domain check on the pure kink.
    period = 2*pi/sqrt(3*model.lam/2)
    td = []
    for A in (.3, .15):
        t, a = sr.kink_time_domain(model.lam, A, t_end=1500., samples=30000)
        env = sr.envelope(t, a, period)
        m = env[:, 0] > 300
        slope = float(np.polyfit(env[m, 0], 1/env[m, 1]**2, 1)[0])
        td.append({'A0': A, 'slope_inverse_A2': slope, 'ratio_to_prediction': slope/cf['Gamma_NL_over_A2'],
                   'envelope_t': env[:, 0].tolist(), 'envelope_A': env[:, 1].tolist()})
    r1, r2 = td[0]['ratio_to_prediction'], td[1]['ratio_to_prediction']
    out['time_domain_kink'] = {'runs': td, 'A2_extrapolated_ratio': r2 - (r1 - r2)*.15**2/(.3**2 - .15**2),
                               'method': 'leapfrog dx=0.05, dt=0.02, damping sponge, projection on psi; slope of 1/A^2 for t>300'}

    # Physical reading and crossover with the linear Higgs width.
    omega2 = state['E']
    G_lin_E = lin['shape_resonance']['Gamma_E']
    cr = sr.crossover(base['P1'], omega2, G_lin_E)
    peak = sqrt(1.5*sqrt(model.lam/2))*.5  # max of the full-line normalised phi profile
    coef = base['Gamma_NL_over_A2']*v
    examples = []
    for dphi in (1e-3, 1., 100., 3000.):
        A = dphi/(peak*v)
        examples.append({'peak_field_GeV': dphi, 'A': A, 'Gamma_NL_GeV': coef*A*A,
                         'inverse_rate_s': HBAR_GEV_S/(coef*A*A)})
    out['physical'] = {'Gamma_NL_GeV_per_A2': coef, 'peak_phi_per_unit_A_GeV': peak*v,
                       'Gamma_NL_formula': 'Gamma_NL=%.6g GeV*(delta_phi_peak/%.6g GeV)^2' % (coef, peak*v),
                       'linear_Higgs_Gamma_GeV': lin['shape_resonance']['physical']['Gamma_GeV'],
                       'crossover_A': cr['A_c'], 'crossover_peak_field_GeV': cr['A_c']*peak*v,
                       'crossover_time_s': HBAR_GEV_S/(cr['linear_rate']*v),
                       'amplitude_law': '1/A(t)^2=1/A0^2+(2 P1/omega^2) t for A>>A_c; exponential Higgs decay below A_c',
                       'examples': examples}
    out['scope'] = ('Leading order in the shape amplitude for the supplied unbiased spectator wall; all three channels in the '
                    'second-harmonic solve. Rectified static part, third-harmonic and O(A^4) frequency shifts are not radiated '
                    'at this order. Floating point with mesh/radius controls, an exact pure-kink closed form and an independent '
                    'nonlinear simulation; no plasma, gauge, angular Higgs or network dynamics.')
    path = ROOT/'receipts/flavor_cosmology/wall_shape_radiation.json'
    path.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: out[k] for k in ('physical_second_harmonic', 'controls', 'cubic_vertex_check')}, indent=1))
    print(json.dumps({k: v_ for k, v_ in out['physical'].items() if k != 'examples'}, indent=1))
    print(out['pure_kink']['relative_difference'], out['pure_kink']['mediator_and_portal_relative_effect'],
          out['Higgs_channel_power_ratio_at_double_portal'], [x['ratio_to_prediction'] for x in td], out['time_domain_kink']['A2_extrapolated_ratio'])


if __name__ == '__main__':
    main()
