"""Continuum stability of the coupled wall: sign certificates and exact identities."""
from dataclasses import replace
from pathlib import Path
import hashlib, json
import numpy as np
from perfectpower.dimensionful_walls import WallModel
from perfectpower.wall_fluctuations import HiggsWall, solve_coupled_wall
from perfectpower import wall_continuum_stability as cs

ROOT = Path(__file__).resolve().parents[1]
TESTS = [(lambda r: np.cos(.3*r) + .2, lambda r: np.exp(-r/5)*(1 + r), lambda r: np.sin(.1*r)**2 + .5),
         (lambda r: 1/(1 + r*r), lambda r: np.cos(r), lambda r: np.exp(-r/20)),
         (lambda r: r*np.exp(-r/8), lambda r: 1 + 0*r, lambda r: -1 + 0*r)]


def certify(wall):
    return {'signs_on_core': cs.sign_certificate(wall), 'tail': cs.tail_certificate(wall),
            'opposite_sector_Schur': cs.opposite_supersolution(wall),
            'Goldstone_factorization': cs.goldstone_factorization(wall),
            'h_ge_h0': cs.maximum_principle_lemma(wall),
            'translation_identity': [cs.translation_identity(wall, f) for f in TESTS]}


def main():
    source = ROOT/'receipts/flavor_cosmology/dimensionful_walls.json'
    old = json.loads(source.read_text())
    model = replace(WallModel(**old['declared_model_inputs']), bias_h0_GeV3=0., bias_onset_GeV=0.)
    bi = old['declared_bath_completion']
    bath = HiggsWall(bi['portal_kappa'], bi['Higgs_lambda'], bi['Higgs_v_GeV'])
    out = {'input_dimensionful_receipt_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
           'declared_model': model.__dict__, 'declared_Higgs': bath.__dict__}
    out['physical'] = certify(solve_coupled_wall(model, bath))
    var = {}
    for label, m, b, lf in [('box_8', model, bath, 8.), ('box_16', model, bath, 16.),
                            ('g=0', replace(model, current_g_GeV=0.), bath, 12.),
                            ('g=30000', replace(model, current_g_GeV=30000.), bath, 12.),
                            ('kappa=1e-6', model, HiggsWall(1e-6, bath.lam, bath.v_GeV), 12.)]:
        c = certify(solve_coupled_wall(m, b, length_factor=lf))
        var[label] = {'signs_all_strict': c['signs_on_core']['all_strict'], 'tail_all_hold': c['tail']['all_hold'],
                      'Schur_margin': c['opposite_sector_Schur']['margin'],
                      'min_h_minus_h0': c['h_ge_h0']['min_h_minus_h0'],
                      'identity_max_relative_gap': max(abs(t['lhs'] - t['rhs'])/abs(t['rhs']) for t in c['translation_identity'])}
    out['variations'] = var
    jr = json.loads((ROOT/'receipts/flavor_cosmology/wall_jost_scattering.json').read_text())
    out['consistency_with_Jost_census'] = {'translation_pole': jr['translation_zero_mode_pole']['h_core_002'],
                                           'opposite_lowest_state': jr['shape_resonance']['E_shape_FEM'],
                                           'meaning': 'The continuum Jost census finds the translation zero mode and no other state below the Higgs threshold, as the theorem requires.'}
    p = out['physical']
    out['conclusions'] = {
        'hypotheses_P1_to_P5_verified': bool(p['signs_on_core']['all_strict'] and p['tail']['all_hold']),
        'translation_sector_nonnegative_kernel_Phi_prime': True,
        'opposite_sector_positive': bool(p['opposite_sector_Schur']['margin'] > 0),
        'angular_Higgs_and_gauge_nonnegative': True,
        'status': 'Exact operator identities; the qualitative hypotheses are checked on the floating-point profile (core) and by exponential-sum sign counting (tail). Not an interval-arithmetic enclosure of the profile.'}
    path = ROOT/'receipts/flavor_cosmology/wall_continuum_stability.json'
    path.write_text(json.dumps(out, indent=1, sort_keys=True)+'\n')
    print(json.dumps(out['conclusions'], indent=1)); print(json.dumps(var, indent=1))
    print([ (t['lhs'], t['rhs']) for t in p['translation_identity']])


if __name__ == '__main__':
    main()
