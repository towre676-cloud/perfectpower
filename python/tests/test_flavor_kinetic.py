"""Independent CP/covariance, positivity and heavy-null-space matching checks."""
from pathlib import Path
import sys
import json
import numpy as np
import mpmath as mp
from scipy.linalg import expm, null_space
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'python'))
from perfectpower.flavor_kinetic import KineticCovariants, fixed_spectrum_bare_metric, array, inner, matrix
from develop_flavor_kinetic import symbolic_spanning_proof, rank_one_source_spectrum


def fixture():
    X = np.diag([1., 2., 3.]).astype(complex)
    Z = np.array([[2, .1j, .3], [.4, 1.5, .2j], [.2j, .3, 1.1]], complex)
    return X, Z, KineticCovariants(X, Z)


def unitary(seed):
    rng = np.random.default_rng(seed)
    a = rng.normal(size=(3, 3))+1j*rng.normal(size=(3, 3))
    return np.linalg.qr(a)[0]


def test_exact_symbolic_spanning_and_CP_identity():
    assert symbolic_spanning_proof()['nine_Hermitian_generator_coordinate_determinant'] == 'tau^3'


def test_nine_generators_span_Hermitian_space():
    _, _, frame = fixture()
    with mp.workdps(90):
        assert max(abs(inner(a, b)-int(i==j)) for i, a in enumerate(frame.basis) for j, b in enumerate(frame.basis)) < mp.mpf('1e-75')
        rng = np.random.default_rng(900)
        a = rng.normal(size=(3, 3))+1j*rng.normal(size=(3, 3)); target = matrix(a+a.conj().T)
        rebuilt = sum((inner(Q, target)*Q for Q in frame.basis), mp.zeros(3))
        assert max(abs(rebuilt[i,j]-target[i,j]) for i in range(3) for j in range(3)) < mp.mpf('1e-75')


def test_fixed_polynomial_recipes_obey_family_and_CP_covariance():
    X, Z, frame = fixture(); U, V, W = [unitary(i) for i in [4, 5, 6]]
    # Test away from the reference point: the real spectral constants stay fixed.
    X, Z = 1.02*X+.03*Z, .98*Z-.01*X
    before = [array(Q) for Q in frame.evaluate(X, Z)]
    transformed = [array(Q) for Q in frame.evaluate(U@X@V.conj().T, U@Z@W.conj().T)]
    cp = [array(Q) for Q in frame.evaluate(X.conj(), Z.conj())]
    phases = [array(Q) for Q in frame.evaluate(X*np.exp(.4j), Z*np.exp(-.7j))]
    for a, b, c, d in zip(before, transformed, cp, phases):
        assert np.max(abs(b-V@a@V.conj().T)) < 2e-11
        assert np.max(abs(c-a.conj())) < 2e-11
        assert np.max(abs(d-a)) < 2e-11


def test_positive_completion_matches_target_and_stays_positive_off_vacuum():
    X, Z, frame = fixture(); U = unitary(17)
    target = U@np.diag([.8, 1.2, 1.6])@U.conj().T
    result = frame.positive_completion(target)
    assert result['error'] < 1e-70
    rng = np.random.default_rng(42)
    for scale in [.0, .3, 1., 2.]:
        x = scale*(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)))
        z = scale*(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)))
        with mp.workdps(90):
            coefficients = [mp.mpf(c) for c in result['real_coefficients']]
            T = sum((c*Q for c, Q in zip(coefficients, frame.evaluate(x, z))), mp.zeros(3))
            B = (mp.eye(3)+T)**2+mp.mpf('.5')*mp.eye(3)
            assert max(abs(B[i,j]-B.H[i,j]) for i in range(3) for j in range(3)) < mp.mpf('1e-65')
            assert min(mp.eighe((B+B.H)/2)[0]) >= mp.mpf('.5')-mp.mpf('1e-60')


def test_bare_metric_matching_against_independent_generalized_null_frame():
    rng = np.random.default_rng(41)
    A = .1*(rng.normal(size=(6,3))+1j*rng.normal(size=(6,3)))
    Y0 = np.diag([.03, .2, .7]).astype(complex)
    K0 = np.eye(3)+A.conj().T@A
    e, U = np.linalg.eigh(K0); Y = Y0@U@np.diag(e**-.5)@U.conj().T
    rotation = expm(.0001*np.array([[0,1j,0],[1j,0,1],[0,-1,0]],complex))
    target = rotation@Y@Y.conj().T@rotation.conj().T
    result = fixed_spectrum_bare_metric(Y0, A, target)
    assert result['target_H_error'] < 1e-70
    # Independently find the heavy superpotential null space, then normalize
    # its metric. This need not choose the same basis as (I,-A).
    heavy = np.hstack([A, np.eye(6)]); N = null_space(heavy)
    metric = np.zeros((9,9),complex); metric[:3,:3] = result['bare_metric']; metric[3:,3:] = np.eye(6)
    K = N.conj().T@metric@N; e, U = np.linalg.eigh(K)
    Y_independent = np.hstack([Y0,np.zeros((3,6))])@N@U@np.diag(e**-.5)@U.conj().T
    assert np.max(abs(Y_independent@Y_independent.conj().T-target)) < 1e-14
    assert np.max(abs(np.linalg.svd(result['matched_Y'],compute_uv=False)-np.linalg.svd(Y,compute_uv=False))) < 1e-14


def test_retained_countermetrics_preserve_six_masses_and_have_four_directions():
    r = json.loads((ROOT/'receipts/m22_interactions/flavor_kinetic.json').read_text())['actual_vacuum']
    assert len(r['twelve_positive_kinetic_countermetrics']) == 12
    assert r['fractional_observable_column_normalized_response_singular_values'][-1] > .5
    assert r['six_fixed_mass_max_log_residual_in_double_SVD'] < 1e-10
    assert min(x['minimum_bare_metric_eigenvalue'] for x in r['twelve_positive_kinetic_countermetrics']) > .99


def test_golden_attack_holds_phase_anchors_and_spectra():
    r = json.loads((ROOT/'receipts/m22_interactions/flavor_kinetic.json').read_text())['golden_chart_counterexample']
    ref = r['reference']
    for case in r['cases']:
        obs = case['observables']
        assert abs(obs['delta_degrees']-66) < 1e-8
        assert max(abs(obs[k]-ref[k]) for k in ['Vus','Vcb']) < 1e-11
        assert np.max(abs(np.log(np.array(obs['spectra'])/ref['spectra']))) < 1e-10
        assert abs(obs['depth']/ref['depth']-1-case['fractional_C_change']) < 1e-9
        assert case['metric_operator_distance_from_identity'] < .0035


def test_source_rank_one_all_eighteen_modes_are_stable():
    r = rank_one_source_spectrum()
    assert len(r['eighteen_real_canonical_mass_coefficients']) == 18
    assert r['eighteen_real_canonical_mass_coefficients'][0] == 3.
    assert abs(r['energy_scaled']+8) < 1e-12


if __name__ == '__main__':
    import unittest
    suite = unittest.TestSuite(unittest.FunctionTestCase(v) for k, v in sorted(globals().copy().items()) if k.startswith('test_'))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(not result.wasSuccessful())
