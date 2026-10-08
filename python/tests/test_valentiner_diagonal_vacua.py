"""Independent branch enumeration and original-tensor derivative checks."""
from itertools import product
from pathlib import Path
import sys
import numpy as np
import sympy as s

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))
from develop_valentiner_diagonal_vacua import (
    X, diagonal_polynomial, full_diagonal_derivatives, determinant_hessians,
    classification_certificate, quotient_certificate, mass_certificates,
    soft_mass_certificate)
from develop_valentiner_link import coefficient_functions


def all_diagonal_roots(a=1.,b=1.,c=0.):
    omega = np.exp(2j*np.pi/3)
    seeds = [np.ones(3,complex)]
    for q in ((-5+1j*np.sqrt(15))/4,(-5-1j*np.sqrt(15))/4):
        for position in range(3):
            seed = np.ones(3,complex); seed[position] = np.sqrt(q)
            seeds.append(seed/seed[0])
    seeds.extend([np.array([1,omega,omega**2]),np.array([1,omega**2,omega])])
    J = diagonal_polynomial()
    weighted_derivative = s.lambdify(X,X[0]*s.diff(J,X[0]),'numpy')
    roots = []
    for seed in seeds:
        for epsilon,delta in product((-1,1),repeat=2):
            direction = seed*np.array([1,epsilon,delta])
            D = np.prod(direction)
            r3 = -a*D/(b*weighted_derivative(*direction)+2*c*D*D)
            for phase in range(3):
                roots.append(direction*(complex(r3)**(1/3))*omega**phase)
    return np.array(roots)


def test_complete_enumeration_and_generic_parameter_equations():
    J = diagonal_polynomial()
    a,b,c = s.symbols('a b c')
    W = a*s.prod(X)+b*J+c*s.prod(X)**2
    gradient = s.lambdify((*X,a,b,c),[s.diff(W,x) for x in X],'numpy')
    for parameters in ((1.,1.,0.),(.7,1.3,.2),(-.4,-.8,1.7)):
        roots = all_diagonal_roots(*parameters)
        assert len(roots) == 108
        distances = np.linalg.norm(roots[:,None,:]-roots[None,:,:],axis=2)+np.eye(108)*100
        assert distances.min() > .05
        assert max(np.linalg.norm(gradient(*root,*parameters)) for root in roots) < 2e-13
    assert classification_certificate()['generic_distinct_diagonal_vacua_including_origin'] == 109


def test_original_tensor_all_nine_F_terms_and_full_hessian():
    _, I6, _ = coefficient_functions()
    grad,H = full_diagonal_derivatives()
    Hd,_ = determinant_hessians()
    evaluate_H = s.lambdify(X,H+Hd,'numpy')
    # One representative of each family, using the original tensor evaluator
    # rather than the diagonal restriction to test all transverse derivatives.
    roots = all_diagonal_roots()
    for root in roots[[0,12,84]]:
        K = np.diag(root)
        def W(matrix):
            return np.linalg.det(matrix)+I6(matrix.conj()).conjugate()
        basis = np.eye(9).reshape(9,3,3)
        eps = 1e-5
        first = [(W(K+eps*E)-W(K-eps*E))/(2*eps) for E in basis]
        assert max(abs(v) for v in first) < 3e-9
        second = np.array([[(W(K+eps*(E+F))-W(K+eps*(E-F))
                             -W(K+eps*(-E+F))+W(K-eps*(E+F)))/(4*eps**2)
                            for F in basis] for E in basis])
        assert np.max(abs(second-evaluate_H(*root))) < 4e-6
    # Certify that finite group/sign/cyclic copies were not silently assumed
    # stable: all 108 matrices are checked numerically in the full field space.
    ranks = [np.count_nonzero(np.linalg.svd(evaluate_H(*root),compute_uv=False)>1e-8) for root in roots]
    assert ranks.count(9) == 84 and ranks.count(6) == 24


def test_exact_mass_and_multiplicity_certificates():
    records = mass_certificates()['benchmark_records']
    assert [r['full_complex_hessian_rank'] for r in records] == [9,6,9]
    algebra = quotient_certificate()
    assert algebra['quotient_dimension'] == 125
    assert algebra['origin_diagonal_local_multiplicity']+108 == 125


def test_universal_soft_mass_energy_order():
    roots = all_diagonal_roots()
    norms = np.sum(abs(roots)**2,axis=1)
    certificate = soft_mass_certificate()
    reference = certificate['numeric_squared_Frobenius_norms']
    assert np.allclose(norms[:12],reference['equal_squares'],atol=1e-13)
    assert np.allclose(norms[12:84],reference['two_equal_squares'],atol=1e-13)
    assert np.allclose(norms[84:],reference['distinct_squares'],atol=1e-13)
    assert reference['two_equal_squares'] > reference['distinct_squares'] > reference['equal_squares']


if __name__ == '__main__':
    import unittest
    suite = unittest.TestSuite(unittest.FunctionTestCase(f) for f in (
        test_complete_enumeration_and_generic_parameter_equations,
        test_original_tensor_all_nine_F_terms_and_full_hessian,
        test_exact_mass_and_multiplicity_certificates,test_universal_soft_mass_energy_order))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(not result.wasSuccessful())
