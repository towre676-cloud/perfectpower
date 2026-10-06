"""Exact mediation identities, complete CP census and scalar-loop closure."""
from pathlib import Path
from fractions import Fraction
import json
import numpy as np
import pytest
from perfectpower.nonet_potential import *
from perfectpower.nonet_mediators import *
from perfectpower.quartic_renormalization import *
from develop_valentiner_nonet_joint import hessian
from valentiner_adjoint_quartics import quartic_projectors
ROOT=Path(__file__).resolve().parents[2]
SAVED=json.loads((ROOT/'receipts/m22_interactions/valentiner_mediator_closure.json').read_text())
SOURCE=json.loads((ROOT/'receipts/m22_interactions/valentiner_nonet_joint.json').read_text())
TABLE=json.loads((ROOT/'receipts/m22_interactions/nonet_scalar_loop_algebra.json').read_text())

@pytest.fixture(scope='module')
def projectors():return np.array(quartic_projectors()[0])

@pytest.fixture(scope='module')
def algebra():
    A=np.zeros((52,52,52))
    for k,i,j,value in TABLE['nonzero_symmetric_products']:A[k,i,j]=A[k,j,i]=float(Fraction(value))
    return A


def test_exact_rank_and_orientation_certificates():
    assert exact_mediator_certificates()==SAVED['matching_certificates']
    assert SAVED['single_mediator_mixed_parameter_Jacobian_rank']==15


def test_exact_complete_251_coefficient_CP_census():
    result=exact_finite_mediator_operator_census();assert result==SAVED['complete_finite_mediator_scalar_census']
    assert result['CP_even']==[3,11,58,3,50]
    assert result['complete_scalar_coefficients_with_Higgs']==251


def test_minimum_mediator_ranks_and_general_matching():
    rng=np.random.default_rng(821)
    for shape in [(4,4),(3,3),(2,5)]:
        C=rng.normal(size=shape);u,d,cert=factorize_cross(C,7)
        assert np.max(abs(C+u@d.T/49))<1e-12
        assert cert['rank']==min(shape)
    C=np.outer([1.,2,3,4],[2.,-3,4,5]);assert factorize_cross(C)[2]['rank']==1
    assert factorize_cross(np.zeros((4,4)))[2]['rank']==0


def test_actual_55_and_27_coordinate_plans(projectors):
    c=np.array(SOURCE['coefficients'])
    assert mediation_plan(c,projectors)['real_mediator_coordinates']==55
    assert mediation_plan(c,projectors,finite_only=True)['real_mediator_coordinates']==27
    with pytest.raises(ValueError):factorize_cross([[1]],mass=-1)


def test_current_jacobian_for_both_UV_plans(projectors):
    rng=np.random.default_rng(881);x=rng.normal(size=20)*.4;c=np.array(SOURCE['coefficients']);eps=1e-6
    for finite in [False,True]:
        plan=mediation_plan(c,projectors,finite_only=finite);J,D=currents(x,plan,projectors)
        fd=np.column_stack([(currents(x+np.eye(20)[j]*eps,plan,projectors)[0]-currents(x-np.eye(20)[j]*eps,plan,projectors)[0])/(2*eps) for j in range(20)])
        assert np.max(abs(fd-D))<1e-8


def test_exact_matching_source_contacts_cancel_intended_cross_terms():
    for value in SAVED['completions'].values():assert value['matching_contact_cross_residual']<1e-12


def test_positive_full_UV_Hessian_and_source_Schur_complement(projectors):
    z=np.array(SOURCE['canonical_coordinates']);c=np.array(SOURCE['coefficients']);portals=np.array(SOURCE['Higgs_portals'])
    H=hessian(lambda z:joint_higgs(z,c,projectors,portals,SOURCE['Higgs_mu2']),z)
    for finite in [False,True]:
        plan=mediation_plan(c,projectors,finite_only=finite);J,D=currents(z[:20],plan,projectors);D=np.column_stack([D,np.zeros(len(D))])
        HH=completed_hessian(H,D,plan['mass']);assert np.linalg.eigvalsh(HH)[0]>1e-5
        schur=HH[:21,:21]-HH[:21,21:]@np.linalg.solve(HH[21:,21:],HH[21:,:21]);assert np.max(abs(schur-H))<1e-12


def test_new_finite_representations_preserve_termwise_mass_phase():
    safe=SAVED['completions']['fermion_safe_finite'];assert safe['neutral_scalar_count']==48
    assert safe['one_loop_paired_vertex_reality_with_new_fermion_vertices_zero']<1e-12
    assert SAVED['matching_certificates']['new_fermion_couplings_for_finite_8prime_9_5pair']==0


def test_allowed_ordinary_adjoint_vertex_does_not_have_that_guarantee():
    exact=exact_heavy_vertex_counterexample();assert exact==SAVED['heavy_vertex_exact_counterexample']
    assert exact['imaginary_part']=='-3/25'
    numerical=SAVED['completions']['universal']['allowed_adjoint_heavy_Yukawa_test']
    assert abs(numerical['one_loop_mass_phase'])>1e-12
    assert numerical['relative_correction_norm']<.05


def test_actual_six_UV_couplings_have_four_mass_fixed_directions():
    assert SAVED['six_UV_current_coupling_fixed_mass_response_singular_values'][-1]>1e-6
    check=SAVED['six_UV_current_coupling_finite_rank_check']
    assert check['finite_implicit_error_spectral_norm']<check['finite_singular_values'][-1]
    for row in SAVED['six_UV_current_coupling_finite_checks']:
        assert row['relative_response_error']<1e-4
        for side in row['sides']:
            assert side['complete_mass_change']<1e-12
            assert side['48_scalar_Hessian_minimum']>1e-5


def test_soft_UV_counterterms_and_EFT_running_are_distinct():
    assert exact_soft_mediator_counterterm_certificate()==SAVED['soft_mediator_counterterm_certificate']
    assert exact_two_scalar_rank_certificate()==SAVED['exact_rank_one_running_certificate']


def test_loop_normalization_for_one_and_eight_real_scalars(algebra):
    assert abs(algebra[0,0,0]-72)<1e-12
    # norm2_up is the square of the eight-component adjoint norm.
    assert abs(algebra[10,10,10]-128)<1e-12


def test_rational_candidate_table_closes_off_grid(projectors,algebra):
    rng=np.random.default_rng(620)
    for _ in range(3):
        x=rng.normal(size=20);p=rng.normal(size=52)*.1;q=rng.normal(size=52)*.1
        H=polynomial_hessians(lambda x:operators(x,projectors)[1][8:],x)
        direct=.5*np.trace(np.einsum('m,mij->ij',p,H)@np.einsum('m,mij->ij',q,H))
        answer=operators(x,projectors)[0][8:]@loop_product(algebra,p,q)
        assert abs(answer-direct)<1e-8*max(abs(direct),1)


def test_nine_operator_closure_is_generated_by_one_finite_channel(algebra):
    B,result=generated_subalgebra(algebra,np.eye(52)[np.array([18,30,57])-8]);assert result['dimension']==9
    support=[OPERATOR_NAMES[i+8] for i in range(52) if np.linalg.norm(B[i])>1e-5]
    assert support==SAVED['scalar_loop_subalgebras']['one_finite_channel']['support']


def test_SU3_unification_preserves_a_five_operator_subalgebra(algebra,projectors):
    assert exact_SU3_27_certificate()==SAVED['exact_SU3_27_certificate']
    v=np.zeros(52);v[49:52]=1
    B,result=generated_subalgebra(algebra,np.vstack([np.eye(52)[10],np.eye(52)[22],v]))
    assert result['dimension']==5
    assert np.linalg.norm(projectors[2]+projectors[3]+projectors[4])**2==pytest.approx(27)
    assert np.linalg.norm(B[11])+np.linalg.norm(B[23])<1e-8


def test_loop_product_is_commutative_and_not_associative(algebra):
    a,b=np.eye(52)[[10,49]];assert np.max(abs(loop_product(algebra,a,b)-loop_product(algebra,b,a)))<1e-12
    lhs=loop_product(algebra,loop_product(algebra,a,b),b);rhs=loop_product(algebra,a,loop_product(algebra,b,b))
    assert np.max(abs(lhs-rhs))>1


def test_radiative_products_generate_omitted_mixed_channels(algebra):
    f=np.eye(52)[49];square=loop_product(algebra,f,f)
    for index in [39,48,50,51]:assert abs(square[index])>.1


def test_generic_polynomial_loop_compiler_on_two_fields():
    def fun(x):
        a,b=x;values=np.array([a**4,a**3*b,a*a*b*b,a*b**3,b**4])
        gradients=np.array([[4*a**3,0],[3*a*a*b,a**3],[2*a*b*b,2*a*a*b],[b**3,3*a*b*b],[0,4*b**3]])
        return values,gradients
    A,c=compile_loop_algebra(fun,2,5,samples=20)
    assert abs(A[0,0,0]-72)<1e-10
    assert max(c['off_grid_relative_errors'])<1e-10
    with pytest.raises(ValueError):compile_loop_algebra(fun,2,5,samples=4)


def test_global_bound_survives_positive_square_completion(projectors):
    rng=np.random.default_rng(510);c=np.array(SOURCE['coefficients']);plan=mediation_plan(c,projectors,finite_only=True)
    for _ in range(4):
        x=rng.normal(size=20);S=rng.normal(size=27);J,_=currents(x,plan,projectors)
        low=potential(x,c,projectors)[0];uv=low+plan['mass']**2*np.linalg.norm(S+J/plan['mass']**2)**2/2
        assert uv>=low


def test_scalar_counterterm_moves_golden_depth_at_fixed_mass():
    drift=SAVED['scalar_loop_fixed_mass_drift'];assert abs(drift['fixed_mass_depth_response_16pi2'])>1
