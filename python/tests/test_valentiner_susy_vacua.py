"""Independent scalar derivative, holomorphy, and full-fermion matching checks."""
import json
from pathlib import Path
import sys
import unittest
import numpy as np
import sympy as s

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT/'python'))
from develop_valentiner_link import coefficient_functions
from develop_valentiner_frames import generators, numeric, group_closure
from develop_valentiner_susy_vacua import adjugate, holomorphic_down_matching, link_branch, source_breaking_branch


def test_full_link_hessian_and_mass_gap():
    _, I6, _ = coefficient_functions()
    a, b, c = -.0324, 1., .2
    r = link_branch(a, b, c)['real_radius']
    def W(K):
        d = np.linalg.det(K)
        return a*d+b*I6(K.conj()).conjugate()+c*d*d
    basis = np.eye(9).reshape(9, 3, 3)
    eps = 2e-5
    H = np.zeros((9, 9), complex)
    for i, E in enumerate(basis):
        for j, F in enumerate(basis):
            H[i, j] = (W(r*np.eye(3)+eps*(E+F))-W(r*np.eye(3)+eps*(E-F))
                       -W(r*np.eye(3)+eps*(-E+F))+W(r*np.eye(3)-eps*(E+F)))/(4*eps**2)
    expected = np.array([[r**4*((8*b+2*c)*np.trace(E)*np.trace(F)+72*b*np.trace(E@F))
                          for F in basis] for E in basis])
    assert np.max(abs(H-expected)) < 3e-9
    masses = np.linalg.svd(H, compute_uv=False)
    assert np.max(abs(masses-np.array([.00972]+[.0072]*8))) < 3e-9


def test_original_sextic_has_no_nonzero_critical_triplet():
    data = json.loads((ROOT/'receipts/m22_interactions/valentiner_invariants.json').read_text())
    x, y, z = s.symbols('x y z')
    f = s.sympify(data['sextic']['polynomial'], locals={'x': x, 'y': y, 'z': z})
    K = s.QQ.algebraic_field(s.sqrt(5), s.I*s.sqrt(3))
    # Independent direct derivatives in the original variables, without squaring
    # coordinates or separating the support cases used in the main calculation.
    basis = s.groebner([s.diff(f, t).subs(x, 1) for t in (x, y, z)], y, z, domain=K)
    assert list(basis) == [1]
    assert s.Poly(f.subs({x: y, y: z, z: x}, simultaneous=True)-f, x, y, z, domain=K).is_zero


def test_holomorphic_cofactor_and_covariance():
    rng = np.random.default_rng(108061)
    K = rng.normal(size=(3, 3))+1j*rng.normal(size=(3, 3))
    gu, gd = numeric(generators()[0]), numeric(generators()[3])
    transformed = gu.conj()@K@gd.T
    assert np.max(abs(adjugate(transformed)-gd.conj()@adjugate(K)@gu.T)) < 2e-13
    assert np.max(abs(K@adjugate(K)-np.linalg.det(K)*np.eye(3))) < 2e-13
    K[:, 2] = K[:, 0]
    assert np.max(abs(K@adjugate(K))) < 2e-13
    # The vertex uses the polynomial K cofactor; anti-holomorphic dependence
    # would fail this complex-direction derivative check.
    E = np.zeros((3, 3)); E[1, 1] = 1
    eps = 1e-5
    real = (adjugate(K+eps*E)-adjugate(K-eps*E))/(2*eps)
    imag = (adjugate(K+1j*eps*E)-adjugate(K-1j*eps*E))/(2j*eps)
    assert np.max(abs(real-imag)) < 2e-10


def test_independent_full_fermion_mass_matching():
    rng = np.random.default_rng(108062)
    K = .1*numeric(generators()[3]).conj()
    source = .15*(rng.normal(size=(3, 3))+1j*rng.normal(size=(3, 3)))
    match = holomorphic_down_matching(K, source)
    v = 1e-6
    full = np.block([[np.zeros((3, 3)), .57*v*np.eye(3), np.zeros((3, 3))],
                     [np.vstack([np.zeros((3, 3)), match['C']]), match['M']]])
    masses = np.linalg.svd(full, compute_uv=False)[-3:]/v
    expected = np.linalg.svd(match['Y'], compute_uv=False)
    assert np.max(abs(masses-expected)) < 3e-10
    assert np.max(abs(holomorphic_down_matching(K, np.zeros((3, 3)))['Y'])) == 0


def test_group_branch_CP_compensation():
    data = json.loads((ROOT/'receipts/m22_interactions/valentiner_cp.json').read_text())
    X = np.array([[complex(s.sympify(z).evalf()) for z in row] for row in data['unitary_CP_matrix']])
    matrices = np.array([numeric(g) for g in group_closure(generators())[0]])
    for index in (0, 1, 4, 103, 501):
        for k in range(3):
            radius = .1*np.exp(2j*np.pi*k/3)
            L = radius*matrices[index]
            cpL = X@L.conj()@X.conj().T
            h = L@np.linalg.inv(cpL)
            assert np.min(np.max(abs(matrices-h), axis=(1, 2))) < 3e-14
            assert np.max(abs(h@cpL-L)) < 3e-14


def test_source_breaking_full_real_hessian():
    data = json.loads((ROOT/'receipts/m22_interactions/valentiner_invariants.json').read_text())
    x, y, z = s.symbols('x y z')
    f = s.sympify(data['sextic']['polynomial'], locals={'x': x, 'y': y, 'z': z})
    value = s.lambdify((x, y, z), f, 'numpy')
    gradient = s.lambdify((x, y, z), [s.diff(f, q) for q in (x, y, z)], 'numpy')
    basis = np.vstack([np.eye(3), 1j*np.eye(3)])/np.sqrt(2)
    eps = 2e-6
    for t in (-26., -24., -22.):
        branch = source_breaking_branch(t=t)
        def V(phi):
            return (np.linalg.norm(gradient(*phi))**2-branch['tachyon_parameter_m2']*np.vdot(phi, phi).real
                    +2*branch['holomorphic_breaking_A']*value(*phi).real)
        p = np.array([.1, 0, 0], complex)
        H = np.array([[(V(p+eps*(E+F))-V(p+eps*(E-F))-V(p+eps*(-E+F))
                       +V(p-eps*(E+F)))/(4*eps**2) for F in basis] for E in basis])
        assert np.max(abs(np.linalg.eigvalsh(H)-np.sort(branch['real_scalar_mass_squared']))) < 3e-11
        assert max(abs((V(p+eps*E)-V(p-eps*E))/(2*eps)) for E in basis) < 3e-13
        assert abs(V(p)-branch['energy']) < 1e-20


if __name__ == '__main__':
    suite = unittest.TestSuite(unittest.FunctionTestCase(f) for f in (
        test_full_link_hessian_and_mass_gap,
        test_original_sextic_has_no_nonzero_critical_triplet,
        test_holomorphic_cofactor_and_covariance,
        test_independent_full_fermion_mass_matching,
        test_group_branch_CP_compensation, test_source_breaking_full_real_hessian))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(not result.wasSuccessful())
