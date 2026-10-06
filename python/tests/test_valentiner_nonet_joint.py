"""Complete scalar basis, stable physical CP and exact CKM constraint geometry."""
from pathlib import Path
import json
import numpy as np
import pytest
from perfectpower.nonet_potential import *
from perfectpower.ckm_constraint_geometry import *
from develop_valentiner_nonet_joint import frame_and_spectrum,source_eigenvalues,source_jacobian,hessian
from develop_valentiner_quantum import standard_CKM
from valentiner_adjoint_quartics import quartic_projectors,adjoint
from develop_valentiner_frames import generators,numeric
ROOT=Path(__file__).resolve().parents[2]
SAVED=json.loads((ROOT/'receipts/m22_interactions/valentiner_nonet_joint.json').read_text())

@pytest.fixture(scope='module')
def tensors():return np.array(quartic_projectors()[0])


def test_exact_complete_character_census():
    assert exact_operator_census()==SAVED['operator_census']
    assert len(OPERATOR_NAMES)==60 and len(MIXED_NAMES)==28


def test_entire_operator_basis_independent(tensors):
    rng=np.random.default_rng(199)
    M=np.array([operators(rng.normal(size=20),tensors)[0] for _ in range(180)])
    assert np.linalg.matrix_rank(M,tol=1e-7)==60


def test_analytic_gradients_all_sixty_operators(tensors):
    rng=np.random.default_rng(922);x=rng.normal(size=20);v,g=operators(x,tensors);h=1e-6
    fd=np.array([(operators(x+np.eye(20)[j]*h,tensors)[0]-operators(x-np.eye(20)[j]*h,tensors)[0])/(2*h) for j in range(20)]).T
    assert np.max(abs(fd-g))<2e-7


def test_full_basis_generator_covariance(tensors):
    x=np.random.default_rng(132).normal(size=20);v=operators(x,tensors)[0]
    for G in generators():
        y=x.copy();D=adjoint(numeric(G));y[2:10]=D@x[2:10];y[12:]=D@x[12:]
        assert np.max(abs(operators(y,tensors)[0]-v))<1e-10


def test_both_sector_Z2_charges(tensors):
    x=np.random.default_rng(192).normal(size=20);v=operators(x,tensors)[0]
    for f in [0,1]:
        y=x.copy();y[10*f:10*f+10]*=-1
        assert np.max(abs(operators(y,tensors)[0]-v))<1e-12


def test_CP_invariance_receipt_and_partner(tensors):
    assert SAVED['operator_CP_error']<1e-12
    CP=np.array(SAVED['CP_adjoint_matrix']);rng=np.random.default_rng(511)
    for _ in range(6):
        x=rng.normal(size=20);y=x.copy();y[2:10]=CP@x[2:10];y[12:]=CP@x[12:]
        assert np.max(abs(operators(y,tensors)[0]-operators(x,tensors)[0]))<1e-10
    # Any unitary frame conjugate has equal CP-even magnitudes and opposite J.
    z=np.array(SAVED['canonical_coordinates']);obs,_,V=frame_and_spectrum(z)
    partner=frame_constraints(V.conj())
    assert np.max(abs(np.array(partner['squared_magnitudes'])-obs['squared_magnitudes']))<1e-14
    assert abs(partner['J']+obs['J'])<1e-14


def test_global_quartic_bound_for_search_family(tensors):
    rng=np.random.default_rng(919)
    for index in range(10):
        c,_=search_coefficients(index)
        assert np.all(c!=0)
        for _ in range(12):
            x=rng.normal(size=20);values=operators(x,tensors)[0]
            assert c[8:]@values[8:] >= (1/6-.12)*(x@x)**2-1e-10


def test_full_higgs_vacuum_is_stationary_and_positive(tensors):
    z=np.array(SAVED['canonical_coordinates']);c=np.array(SAVED['coefficients']);p=np.array(SAVED['Higgs_portals'])
    fun=lambda z:joint_higgs(z,c,tensors,p,SAVED['Higgs_mu2'])
    assert np.linalg.norm(fun(z)[1])<2e-10
    assert np.linalg.eigvalsh(hessian(fun,z))[0]>1e-5
    assert abs(fun(z)[0]-SAVED['energy'])<1e-12


def test_light_current_recovers_unitary_frame_and_physical_CP():
    z=np.array(SAVED['canonical_coordinates']);obs,sectors,V=frame_and_spectrum(z)
    qu,qd=[s['doublet_frame'] for s in sectors]
    raw=qu.conj().T@qd;weights=[np.linalg.norm(Q,axis=0) for Q in [qu,qd]]
    assert np.max(abs(raw/np.outer(*weights)-V))<1e-14
    assert abs(obs['J'])>1e-5
    assert min(np.min(np.diff(s['masses'])) for s in sectors)>1e-5
    assert abs(obs['unitarity_polynomial_scaled_residual'])<1e-10


def test_scalar_eigenmode_one_loop_protection():
    assert SAVED['maximum_one_loop_paired_vertex_imaginary_part']<1e-12
    assert max(abs(s['tree_mass_determinant_imag']) for s in SAVED['fermion_spectra'])<1e-15
    assert min(s['tree_mass_determinant_real'] for s in SAVED['fermion_spectra'])>0


def test_all_four_observables_move_at_fixed_mass():
    assert min(SAVED['fixed_spectrum_response_singular_values'])>1e-4
    assert SAVED['fixed_spectrum_linear_error']<1e-10
    check=SAVED['fixed_spectrum_finite_rank_check']
    assert check['response_discrepancy_spectral_norm']<check['singular_values'][-1]
    for row in SAVED['fixed_spectrum_finite_checks']:
        assert row['relative_response_error']<1e-4
        for side in row['sides']:
            assert side['maximum_mass_change']<1e-10
            assert side['hessian_min']>1e-5


def test_source_eigenvalue_jacobian(tensors):
    x=np.array(SAVED['canonical_coordinates'][:20]);h=1e-6
    fd=np.column_stack([(source_eigenvalues(x+np.eye(20)[j]*h)-source_eigenvalues(x-np.eye(20)[j]*h))/(2*h) for j in range(20)])
    assert np.max(abs(fd-source_jacobian(x)))<1e-8


def test_golden_and_phase_equations_accept_target_and_reject_branch():
    C=(3-np.sqrt(5))/2;V=standard_CKM(.225,C*.225*.04,.04,np.deg2rad(66))
    r=frame_constraints(V)
    assert abs(r['golden_scaled_residual'])<1e-12
    assert abs(r['phase_scaled_residual'])<1e-9
    assert r['small_golden_branch'] and r['positive_66_branch']
    assert not SAVED['observables']['small_golden_branch']
    assert not SAVED['observables']['positive_66_branch']


def test_invariant_constraints_do_not_depend_on_rephasing():
    V=standard_CKM();rng=np.random.default_rng(817);p=np.exp(1j*rng.normal(size=6))
    W=np.diag(p[:3])@V@np.diag(p[3:]);a=frame_constraints(V);b=frame_constraints(W)
    for key in ['depth','J','cos_standard_phase','golden_scaled_residual','phase_scaled_residual']:
        assert abs(a[key]-b[key])<1e-11
    with pytest.raises(ValueError):frame_constraints(V*.9)


def test_actual_polynomial_engine_derives_elliptic_connection():
    assert exact_geometry_certificate()==SAVED['geometry']
    assert elliptic_slice(Q(1,100000),Q(73,500))==SAVED['rational_elliptic_example']
    with pytest.raises(ValueError):elliptic_slice(Q(1,10),Q(1,10))


def test_exact_restricted_trace_potential_obstruction():
    assert exact_trace_potential_certificate()['quartic_moment_hessian_rank_at_most']==1
