"""Arb-certified translation-complement gap of the interval-certified wall."""
from pathlib import Path
import hashlib, json
from perfectpower import wall_stability_certified as wsc

ROOT = Path(__file__).resolve().parents[1]


def main():
    seed_path = ROOT/'receipts/flavor_cosmology/wall_profile_interval_seed.json'
    seed = json.loads(seed_path.read_text())
    out = {'seed_sha256': hashlib.sha256(seed_path.read_bytes()).hexdigest(),
           'identities': wsc.exact_identities()}
    out['certificate_160_bits'] = wsc.certify_gap(seed, precision=160)
    replay = wsc.certify_gap(seed, precision=192)
    out['replay_192_bits_gamma_lower'] = replay['bounds_Arb']['gamma_lower']
    rejected = {}
    for label, kw in (('tau_0.999', {'tau': '0.999'}), ('theta_0.9999999', {'theta': '0.9999999'})):
        try:
            wsc.certify_gap(seed, **kw)
            rejected[label] = 'accepted'
        except ArithmeticError as exc:
            rejected[label] = 'rejected: %s' % exc
    out['deliberately_bad_splittings'] = rejected
    b = out['certificate_160_bits']['bounds_display_float']
    out['statement'] = (
        'For the exact whole-line wall certified by wall_profile_intervals (rational inputs, source quartic interval), '
        'the radial Hessian L on L2(R)^3 satisfies <f,Lf> >= gamma k2 ||f||^2 for every f orthogonal to the translation '
        'mode Phi\', with gamma>%.6f (x units, k2=lambda/2). Hence L>=0, ker L=span(Phi\') and the radial spectrum in '
        '(0, %.4f GeV^2) is empty; the essential spectrum begins at most at %.6f, so the bound is within %.3f percent '
        'of the Higgs continuum edge.' % (b['gamma_lower'], b['gap_GeV2_lower'], b['essential_edge_upper'],
                                          100*(1 - b['gamma_over_edge_lower'])))
    out['scope'] = ('Linear (Hessian) spectrum of the radial three-field operator of the certified retuned-quartic wall '
                    '(lambda=1.76188164948e-5 +/- 1e-15, alpha=0.1, mu=10, lambda_H=0.13, h0=0.0082, kappa=1e-7). '
                    'Not the declared lambda=0.1 wall, whose stability remains the floating-point theorem of '
                    'wall_continuum_stability. Angular/gauge sectors are not re-certified here; no nonlinear, '
                    'thermal or quantum stability; Python+Arb trust base, no Lean check.')
    path = ROOT/'receipts/flavor_cosmology/wall_stability_certified.json'
    path.write_text(json.dumps(out, indent=1, sort_keys=True) + '\n')
    print(json.dumps(b, indent=1)); print(out['statement']); print(rejected)


if __name__ == '__main__':
    main()
