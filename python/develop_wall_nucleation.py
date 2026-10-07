"""Finite-temperature transition character and nucleation of the biased CP vacua."""
from dataclasses import replace
from pathlib import Path
from math import sqrt, pi, log
import hashlib, json
import numpy as np
from scipy.integrate import quad
from perfectpower.dimensionful_walls import WallModel, radiation_H, MPL_REDUCED_GEV
from perfectpower.wall_fluctuations import HiggsWall
from perfectpower import wall_nucleation as wn

ROOT = Path(__file__).resolve().parents[1]
TEMPERATURES = (0.03, 1., 100., 1000., 2999.)


def gstar(T):
    """Declared radiation degrees: SM plus the singlet above 0.2 GeV, 10.75 below."""
    return 107.75 if T > .2 else 10.75


def heavy_mixing_mass_shift(model, T):
    """phi-mass^2 shift from the thermal loop of the heavy mediator, via its mixing.

    The heavy eigenvalue is M^2+4 g^2 phi^2/M^2+O(phi^4), so
    delta m_phi^2=(8 g^2/M^2)(T^2/2pi^2) dJ_B/dy at y=M^2/T^2, with
    dJ_B/dy=(1/2)int x^2/(sqrt(x^2+y)(e^{sqrt(x^2+y)}-1)) dx.
    """
    y = (model.heavy_mass_GeV/T)**2
    dJ = quad(lambda x: x*x/(sqrt(x*x + y)*np.expm1(sqrt(x*x + y))), 0, 200)[0]/2
    return 8*model.current_g_GeV**2/model.heavy_mass_GeV**2*T*T/(2*pi*pi)*dJ


def main():
    source = ROOT/'receipts/flavor_cosmology/dimensionful_walls.json'
    old = json.loads(source.read_text())
    biased = WallModel(**old['declared_model_inputs'])
    bi = old['declared_bath_completion']
    bath = HiggsWall(bi['portal_kappa'], bi['Higgs_lambda'], bi['Higgs_v_GeV'])
    v, lam, c = biased.v_GeV, biased.lam, biased.thermal_c
    out = {'input_dimensionful_receipt_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
           'declared_model': biased.__dict__, 'declared_Higgs': bath.__dict__}

    # 1. Character of the CP transition.
    pt = wn.perturbative_transition(lam, v, c)
    scan = {str(l): wn.perturbative_transition(l, v, l/4)['loop_parameter'] for l in (.01, .1, 1.)}
    Tc = pt['Tc']
    out['CP_transition'] = {
        'declared_thermal_c': c, 'one_loop_Debye_lam_over_4_plus_kappa_over_3': lam/4 + bath.portal/3,
        'resummed_perturbative': pt, 'loop_parameter_by_lambda': scan,
        'heavy_mediator_phi_mass2_shift_over_cT2_at_Tc': heavy_mixing_mass_shift(biased, Tc)/(c*Tc*Tc),
        'heavy_mass_over_Tc': biased.heavy_mass_GeV/Tc,
        'gauge_dependence': 'phi is a gauge singlet: the one-loop potential along phi is gauge independent. Gauge fields enter only through Higgs loops, which are suppressed by kappa=1e-7.',
        'conclusion': 'The resummed one-loop barrier comes only from the phi self-loop. Its loop parameter lam T/(8 pi m) at the would-be broken minimum is the same for every lam, so it is never parametrically perturbative. A real Z2 scalar has a continuous (3D Ising universality) transition, so no bubbles nucleate at the CP transition and the walls form by the Kibble mechanism.'}

    # 2. Conditional Kibble-Zurek domain size (declared dynamical exponents).
    H_c = radiation_H(Tc, gstar(Tc))
    xi0 = 1/(sqrt(2*c)*Tc)
    nu = .63
    kz = []
    for z in (1., 2.):
        xi = xi0*((1/H_c)/xi0)**(nu/(1 + z*nu))
        kz.append({'z': z, 'xi_KZ_GeV_inv': xi, 'domains_per_Hubble_length': 1/(H_c*xi)})
    out['Kibble_Zurek_estimate'] = {'nu_3D_Ising': nu, 'tau_Q': '1/H(Tc)', 'xi0_tau0': '1/(sqrt(2c) Tc)',
                                    'H_Tc_GeV': H_c, 'rows': kz,
                                    'scope': 'Order-of-magnitude freeze-out estimate with declared exponents and microscopic scales; plasma dynamics not simulated.'}

    # 3. Bounces and their checks.
    table = []
    for e in (.01, .02, .05, .1, .2, .3, .35, .38, .3845):
        for d in (3, 4):
            b = wn.bounce(e, d)
            table.append({'eps': e, 'd': d, 's': b['s'], 'thin_wall_ratio': b['s']/wn.thin_wall(e, d),
                          'virial_defect': b['virial_defect'], 'radius': b['radius_half_point']})
    out['bounce_table'] = table
    out['spinodal'] = {'eps_sp': wn.EPS_SPINODAL,
                       'cubic_bounce': {str(d): wn.cubic_bounce(d)['s'] for d in (3, 4)},
                       'C_exact': {str(d): wn.spinodal_constant_exact(d) for d in (3, 4)},
                       'approach': {str(d): wn.spinodal_constant(d) for d in (3, 4)}}

    # 4. Critical bias for nucleation versus declared bias, with a prefactor band.
    rows = []
    bounces = {}
    for T in TEMPERATURES:
        vT = v*sqrt(1 - c*T*T/(lam*v*v))
        H = radiation_H(T, gstar(T))
        h_decl = biased.h(T)
        row = {'T_GeV': T, 'v_T_GeV': vT, 'H_GeV': H, 'gstar': gstar(T),
               'eps_declared': h_decl/(lam*vT**3), 'h_spinodal_GeV3': wn.EPS_SPINODAL*lam*vT**3}
        for d, scale, Hu in ((3, vT/(sqrt(lam)*T), H/T), (4, 1/lam, H/vT)):
            res = {}
            for band in (-20., 0., 20.):
                s_star, S_star = wn.nucleation_threshold(d, scale, Hu, prefactor_band=band)
                e_star, how = wn.critical_eps(s_star, d)
                res[str(band)] = {'S_star': S_star, 's_star': s_star, 'eps_star': e_star, 'method': how}
            mid = res['0.0']
            mid['h_star_GeV3'] = mid['eps_star']*lam*vT**3
            mid['h_star_over_h_declared'] = mid['h_star_GeV3']/h_decl
            mid['eps_star_over_eps_spinodal'] = mid['eps_star']/wn.EPS_SPINODAL
            row['d%d' % d] = res
            if mid['method'] == 'bounce':
                bounces[(T, d)] = (mid['eps_star'], vT)
        row['easier_channel'] = 'thermal_O3' if row['d3']['0.0']['eps_star'] < row['d4']['0.0']['eps_star'] else 'quantum_O4'
        rows.append(row)
    out['nucleation_threshold'] = rows

    # 5. Three-field sandwich S1<=S3<=S1(1+delta)^{d/2} on the critical bounces.
    a = biased.current_g_GeV/v; mu = biased.heavy_mass_GeV/v
    beta = bath.portal/bath.lam; h0 = bath.v_GeV/v
    sandwich = []
    for (T, d), (e, vT) in sorted(bounces.items()):
        b = wn.bounce(e, d)
        delta = wn.lifting_ratio(b['profile_r'], b['profile_phi'], d, a, mu, beta, h0, vT/v)
        sandwich.append({'T_GeV': T, 'd': d, 'eps': e, 'delta': delta, 'upper_factor': (1 + delta)**(d/2)})
    out['three_field_sandwich'] = {
        'statement': 'For d=3,4 the bounce minimises R=(2/d)((d-2)/d)^{(d-2)/2} T^{d/2}/(-U)^{(d-2)/2} over configurations with U<0 (Coleman-Glaser-Martin). The three-field potential is the biased source quartic plus two nonnegative squares and has the same false-vacuum energy. So projection gives S1<=S3, and the valley lift (S=-a u^2/mu^2, eta^2=eta0^2-beta(u^2-1)) gives S3<=S1(1+delta)^{d/2}.',
        'hypothesis': 'The CGM reduced-functional characterisation of the least-action bounce, for the three-component field.',
        'rows': sandwich}

    out['conclusions'] = {
        'CP_transition_first_order_controlled': False,
        'bubble_nucleation_at_CP_transition': False,
        'biased_vacuum_nucleation_with_declared_bias': False,
        'declared_bias_shortfall_orders_of_magnitude': float(min(np.log10(r['d4']['0.0']['h_star_over_h_declared']) for r in rows)),
        'quantum_threshold_fraction_of_spinodal': rows[0]['d4']['0.0']['eps_star_over_eps_spinodal']}
    out['scope'] = ('Supplied spectator model only. Leading resummed high-T potential along the singlet direction; single-field '
                    'bounces with the three-field sandwich; the fluctuation determinant is a declared band of exp(+-20). '
                    'One-loop zero-temperature Coleman-Weinberg corrections (relative size lam/16pi^2) and two-loop thermal '
                    'terms are not included. No lattice, real-time or network simulation.')
    path = ROOT/'receipts/flavor_cosmology/wall_nucleation.json'
    path.write_text(json.dumps(out, indent=2, sort_keys=True)+'\n')
    print(json.dumps(out['CP_transition'], indent=1)[:1500])
    print(json.dumps(out['conclusions'], indent=1))
    for r in rows:
        print(r['T_GeV'], r['easier_channel'], 'eps3*', r['d3']['0.0']['eps_star'], r['d3']['0.0']['method'],
              'eps4*', r['d4']['0.0']['eps_star'], 'ratio', r['d4']['0.0']['h_star_over_h_declared'],
              'band4', r['d4']['-20.0']['eps_star'], r['d4']['20.0']['eps_star'])
    print(sandwich, kz)


if __name__ == '__main__':
    main()
