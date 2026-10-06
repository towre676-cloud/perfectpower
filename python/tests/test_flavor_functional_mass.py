"""Functional mass protection, hierarchy and the permitted cross-source boundary."""
import numpy as np
import pytest
from perfectpower.flavor_functional_mass import *
from perfectpower.flavor_hermitian import paired_vertex_reality
from perfectpower.flavor_quantum import scalar_threshold
from develop_flavor_functional_mass import hermitian_basis,build_receipt

@pytest.mark.parametrize('seed',[17,33,61])
def test_frechet_derivatives_for_noncommuting_complex_variations(seed):
    rng=np.random.default_rng(seed);X=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));C=(X+X.conj().T)/2
    H,K=hermitian_basis()[3],hermitian_basis()[4];p=[.3,0,.2,0,.03];e=1e-5
    derivative=(matrix_polynomial(C+e*H,p)-matrix_polynomial(C-e*H,p))/(2*e)
    assert np.max(abs(derivative-polynomial_variation(C,H,p)))<1e-9
    second=(polynomial_variation(C+e*K,H,p)-polynomial_variation(C-e*K,H,p))/(2*e)
    assert np.max(abs(second-polynomial_second_variation(C,H,K,p)))<1e-9
    assert np.max(abs(polynomial_second_variation(C,H,K,p)-polynomial_second_variation(C,K,H,p)))<1e-12

@pytest.mark.parametrize('degenerate',[False,True])
def test_first_order_threshold_reality_with_all_hermitian_modes(degenerate):
    rng=np.random.default_rng(62);X=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));U,_=np.linalg.qr(X)
    C=U@np.diag([.2,.2 if degenerate else .7,1.3])@U.conj().T;p=[.7,0,.1,0,.03]
    q=functional_spectrum(C,.3,p);G=functional_vertices(C,.07*hermitian_basis(),p,.1)
    X=rng.normal(size=(10,10));H=X.T@X+.2*np.eye(10);O=np.linalg.eigh(H)[1];mixed=np.einsum('ab,aij->bij',O,G)
    assert paired_vertex_reality(q,mixed)<1e-15
    assert np.max(abs(q['left'].conj().T@q['mass_matrix']@q['right']-np.diag(q['masses'])))<2e-15
    r=scalar_threshold(q['mass_matrix'],G,H);assert abs(r['delta_theta'])<1e-16 and abs(r['UV_phase_coefficient'])<1e-16


def test_even_function_preserves_shaping_sign_and_positive_tree_determinant():
    C=np.diag([-10.,-20.,30.]);p=[.101,0,-.002,0,.00001]
    assert matrix_polynomial(-C,p)==pytest.approx(matrix_polynomial(C,p))
    q=functional_spectrum(C,1,p);assert np.linalg.det(q['mass_matrix']).real>0 and abs(np.linalg.det(q['mass_matrix']).imag)<1e-20
    cert=positive_quartic_certificate();assert cert['source_trace']=='0' and cert['fermion_operator_dimension']==7
    assert np.all(q['masses'][:3]<1) and np.all(q['masses'][3:]>10)
    assert q['masses'][1]/q['masses'][0]>440 and q['masses'][2]/q['masses'][1]>104/23
    assert np.min(np.diag(q['doublet_frame'].conj().T@q['doublet_frame']).real)>.99


def test_same_source_seagull_phase_and_hermitian_vacuum_shift():
    C=np.diag([-.3,.7,1.1]);p=[1.,0,-.02,0,.1];M=matrix_polynomial(C,p)
    K=polynomial_second_variation(C,hermitian_basis()[3],hermitian_basis()[4],p)
    assert abs(np.trace(np.linalg.solve(M,K)).imag)<1e-16
    for H in hermitian_basis():assert abs(np.trace(np.linalg.solve(M,polynomial_variation(C,H,p))).imag)<1e-16


def test_charge_transitivity_and_quadratic_operator_census():
    c=charge_and_operator_certificate();assert c['linear_source_heavy_mass_forbidden_by_existing_Z2']
    assert len(c['single_source_contractions'])==7 and c['two_sector_total']==28
    # Separate signs forbid mixed source products, permit each sector square.
    signs=[(-1,1),(1,-1)]
    assert [tuple(x*x for x in v) for v in signs]==[(1,1),(1,1)]
    assert tuple(x*y for x,y in zip(*signs))==(-1,-1)


def test_allowed_opposite_source_breaks_first_order_reality_with_small_threshold():
    r=wrong_source_example();assert r['tree_determinant_phase']==pytest.approx(0,abs=1e-16)
    assert r['heavy_mass_minimum_eigenvalue']>1 and r['source_mass_commutator_norm']>.001
    assert r['source_CP_cycle']!=0 and r['relative_correction_norm']<.001
    assert r['maximum_imaginary_vertex_pair']>1e-4 and abs(r['first_order_neutral_scalar_phase'])>6e-8
    assert abs(r['UV_phase_coefficient'])<1e-16
    assert r['first_order_neutral_scalar_phase']==pytest.approx(float(high_precision_wrong_source_phase()['first_order_B0_phase']),abs=1e-18)
    exact=exact_wrong_source_resolvent_certificate();assert exact['nonzero_exactly'] and exact['tree_determinant_positive']


def test_four_orientation_directions_survive_at_fixed_full_spectrum():
    q=functional_spectrum(np.diag([-10.,-20.,30.]),1,[.101,0,-.002,0,.00001]);w=np.sqrt(np.diag(q['doublet_frame'].conj().T@q['doublet_frame']).real)
    r=orientation_response(w,w);assert r['Jacobian_rank']==4 and abs(r['Jacobian_determinant'])>1e-5


def test_domain_rejections():
    with pytest.raises(ValueError):functional_spectrum(np.eye(3),0,[1])
    with pytest.raises(ValueError):functional_spectrum(np.eye(3),1,[-1])
    with pytest.raises(ValueError):matrix_polynomial(np.array([[0,1],[0,0]]),[1])
    with pytest.raises(ValueError):polynomial_variation(np.eye(3),np.eye(2),[1,0,.1])
    with pytest.raises(ValueError):matrix_polynomial(np.eye(3),[float('nan')])


def test_exact_group_average_and_scalar_operator_running():
    c=exact_quadratic_source_multiplicities();assert c['group_order']==1080
    assert [c['exact_singlet_multiplicity'],c['exact_ordinary_adjoint_multiplicity']]==[4,3]
    t=exact_cross_source_running_tensor();assert t['exact_general_Hermitian_tensor_identity']
    assert t['scalar_loop_beta_times_16pi_squared']=='10*kappa*lambda/3'
