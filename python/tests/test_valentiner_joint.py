"""Independent covariance, derivative, CP and stationary-branch checks."""
import json
from pathlib import Path
import sys
import unittest
import numpy as np
import sympy as s

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'python'))
from valentiner_joint import pack, unpack, operator_basis, potential, base_potential, hessian, solve, quarks, source_poly
from develop_valentiner_frames import generators, numeric
from develop_valentiner_joint import exact_complex_census, nonorthogonal_start
from develop_valentiner_link import coefficient_functions


def fixture():
    r = json.loads((ROOT/'receipts/m22_interactions/valentiner_joint.json').read_text())
    return r, np.array(r['vacua'][2]['field_coordinates']), np.array([q['scaled_coefficient'] for q in r['operators']])


def test_exact_character_census_independent_of_trace_basis():
    assert exact_complex_census()['complex_polynomial_dimensions'] == {2: 7, 3: 2, 4: 41, 5: 14, 6: 223}
    x = np.random.default_rng(1).normal(size=54)
    d, n, _ = operator_basis(x)
    assert {k: d.count(k) for k in set(d)} == {2: 7, 3: 1, 4: 41, 5: 7, 6: 207}
    assert len(set(n)) == 263


def test_exact_polynomial_independence_modular_certificate():
    from valentiner_joint_certificate import independence_certificate
    certificate = independence_certificate()
    assert [(q['degree'], q['rank']) for q in certificate['balanced_basis_witnesses']] == [(2, 7), (4, 41), (6, 199)]


def test_every_operator_family_shaping_and_CP_covariance():
    rng = np.random.default_rng(77); x = rng.normal(size=54)*.3
    L, p = unpack(x); baseline = operator_basis(x)[2]
    gs = [numeric(g) for g in generators()]
    for gu, gd in [(g, np.eye(3)) for g in gs]+[(np.eye(3), g) for g in gs]:
        q = np.vstack([(gu@p[:3].T).T, (gd@p[3:].T).T])
        assert np.max(abs(operator_basis(pack(gu@L@gd.conj().T, q))[2]-baseline)) < 2e-10
    for i in range(6):
        q = p.copy(); q[i] *= np.exp(2j*np.pi/6)
        assert np.max(abs(operator_basis(pack(L, q))[2]-baseline)) < 2e-10
    cp = json.loads((ROOT/'receipts/m22_interactions/valentiner_cp.json').read_text())
    X = np.array([[complex(s.sympify(t).evalf()) for t in row] for row in cp['unitary_CP_matrix']])
    cp_x = pack(X@L.conj()@X.conj().T, (X@p.conj().T).T)
    assert np.max(abs(operator_basis(cp_x)[2]-baseline)) < 2e-10
    assert abs(base_potential(cp_x)[0]-base_potential(x)[0]) < 2e-8


def test_all_operator_derivatives_against_real_displacements():
    rng = np.random.default_rng(991); x = rng.normal(size=54)*.3; e = rng.normal(size=54)
    _, _, _, g = operator_basis(x, True); eps = 1e-6
    numerical = (operator_basis(x+eps*e)[2]-operator_basis(x-eps*e)[2])/(2*eps)
    assert np.max(abs(numerical-g@e)) < 2e-8


def test_base_potential_against_independent_tensor_contraction():
    _, I6, _ = coefficient_functions(); rng = np.random.default_rng(885)
    x = rng.normal(size=54)*.25; L, p = unpack(x); eps = 1e-6
    def W(L):
        D = np.linalg.det(L)
        return -32.4*D+I6(L)+.2*D*D
    basis = np.eye(9).reshape(9, 3, 3)
    g = np.array([(W(L+eps*E)-W(L-eps*E))/(2*eps) for E in basis])
    value = np.vdot(g, g).real+sum(np.vdot(source_poly(z)[1], source_poly(z)[1]).real
                                  -36*np.vdot(z, z).real-48*source_poly(z)[0].real for z in p)
    assert abs(base_potential(x)[0]-value) < 3e-8
    e = rng.normal(size=54)
    fd = (base_potential(x+eps*e)[0]-base_potential(x-eps*e)[0])/(2*eps)
    assert abs(fd-base_potential(x)[1]@e) < 2e-6


def test_shared_column_CP_determinant_identity():
    x, _ = nonorthogonal_start(); _, p = unpack(x); C = p[:3].T
    G = C.conj().T@C; a = np.array([.03, .2, 1.]); b = np.array([.04, .5, 1.3])
    Hu, Hd = C@np.diag(a)@C.conj().T, C@np.diag(b)@C.conj().T
    expected = 2j*np.linalg.det(G)*(a[0]*b[1]-b[0]*a[1])*(a[1]*b[2]-b[1]*a[2])*(a[2]*b[0]-b[2]*a[0])*np.imag(G[0, 1]*G[1, 2]*G[2, 0])
    assert abs(np.linalg.det(Hu@Hd-Hd@Hu)-expected) < 1e-14
    assert abs(expected.imag) > 1e-9


def test_full_stationarity_and_positive_hessian_in_retained_vacuum():
    _, x, c = fixture()
    assert np.max(abs(potential(x, c)[1])) < 1e-7
    assert np.linalg.eigvalsh(hessian(x, c))[0] > 100
    assert np.all(c != 0)
    record = quarks(x, np.array([.007, .05, .9, .02, .2, .85]))
    assert max(record[k] for k in ['Vus', 'Vcb', 'Vub']) < .03
    assert abs(record['J']) > 1e-10


def test_finite_operator_deformation_is_a_fresh_minimum():
    r, x, c = fixture(); names = [q['name'] for q in r['operators']]; j = names.index('X02')
    c[j] += .01*abs(c[j]); z, result = solve(x, c)
    assert result['stationarity_max'] < 1e-7 and result['minimum_real_hessian_eigenvalue_scaled'] > 100
    target = next(q for q in r['fully_reminimized_one_percent_deformations'] if q['operator'] == 'X02' and q['coefficient_fractional_change'] > 0)
    obs = quarks(z, np.array(r['quark_column_weights']))
    assert abs(obs['depth']-target['observables']['depth']) < 1e-7
    assert abs(obs['depth']-r['vacua'][2]['observables']['depth']) > .01
    matched = quarks(z, np.array(target['same_six_masses_refitted_weights']))
    masses = np.array(matched['spectra']); baseline_masses = np.array(r['vacua'][2]['observables']['spectra'])
    assert np.max(abs(np.log(masses/baseline_masses))) < 1e-8
    assert abs(matched['depth']-r['vacua'][2]['observables']['depth']) > .5


def test_mass_conditioned_response_and_independent_weak_basis_CP():
    from valentiner_joint import canonical_mediator, holomorphic_down_matching, RHO
    r, x, _ = fixture(); w = np.array(r['quark_column_weights']); L, phi = unpack(x)
    Yu = canonical_mediator(.9*np.eye(3), RHO*phi[:3].T@np.diag(w[:3]), h=.6)['Y']
    Yd = holomorphic_down_matching((RHO*L).conj(), (RHO*phi[3:].T@np.diag(w[3:])).conj())['Y']
    Hu, Hd = Yu@Yu.conj().T, Yd@Yd.conj().T
    diff = lambda M: np.prod([b-a for i, a in enumerate(np.linalg.eigvalsh(M)) for b in np.linalg.eigvalsh(M)[i+1:]])
    predicted = 2*quarks(x, w)['J']*diff(Hu)*diff(Hd)
    assert abs(np.linalg.det(Hu@Hd-Hd@Hu).imag/predicted-1) < 2e-5
    response = r['local_response']
    O = np.array(response['jacobian']); M = np.array(response['six_log_mass_jacobian'])
    correction = np.linalg.solve(M[:, 15:], -M[:, :15])
    assert np.max(abs(M[:, :15]+M[:, 15:]@correction)) < 1e-12
    held = O[:, :15]+O[:, 15:]@correction
    q = r['vacua'][2]['observables']; held /= np.array([abs(q[k]) for k in ['Vus', 'Vcb', 'Vub', 'J']])[:, None]
    assert np.linalg.svd(held/np.linalg.norm(held, axis=0), compute_uv=False)[-1] > .05


def test_independent_weights_preserve_orthogonal_and_move_nonorthogonal_frames():
    x, _ = nonorthogonal_start(); _, p = unpack(x); C = p[:3].T
    def projectors(C, w):
        _, U = np.linalg.eigh(C@np.diag(w)@C.conj().T)
        return [np.outer(U[:, i], U[:, i].conj()) for i in range(3)]
    a, b = [.03, .2, 1.], [.03, .24, 1.]
    assert max(np.linalg.norm(q-r) for q, r in zip(projectors(np.eye(3), a), projectors(np.eye(3), b))) == 0
    assert max(np.linalg.norm(q-r) for q, r in zip(projectors(C, a), projectors(C, b))) > .01
    E = [np.outer(C[:, i], C[:, i].conj()) for i in range(3)]
    assert np.linalg.norm(E[0]@E[1]-E[1]@E[0]) > .1


if __name__ == '__main__':
    suite = unittest.TestSuite(unittest.FunctionTestCase(v) for k, v in sorted(globals().copy().items()) if k.startswith('test_'))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(not result.wasSuccessful())
