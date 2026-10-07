from pathlib import Path
import json
import numpy as np
import pytest
from perfectpower.flavor_scalar_feedback import *

ROOT=Path(__file__).resolve().parents[2]

@pytest.fixture(scope='module')
def model():
    b=json.loads((ROOT/'receipts/m22_interactions/flavor_singlet_mediation.json').read_text())['singlet_finite_UV']
    return SingletScalarModel(b)

def packet():return json.loads((ROOT/'receipts/m22_interactions/flavor_scalar_feedback.json').read_text())

def test_spectral_trace_gradient_independent_difference():
    rng=np.random.default_rng(119);B=rng.normal(size=(5,5));H=B.T@B+np.eye(5);A=rng.normal(size=(5,5));A=(A+A.T)/2;e=1e-5
    exact=scalar_CW_gradient(H,[A],.8)[0];finite=(scalar_CW(H+e*A,.8)-scalar_CW(H-e*A,.8))/(2*e)
    assert exact==pytest.approx(finite,rel=1e-8,abs=1e-10)

def test_scale_counterterm_identity():
    H=np.diag([.2,.7,1.3]);e=1e-5
    d=(scalar_CW(H,np.exp(e))-scalar_CW(H,np.exp(-e)))/(2*e)
    assert 16*np.pi**2*d+np.trace(H@H)/2==pytest.approx(0,abs=1e-10)

def test_full_non_Gaussian_gradient_and_hessian(model):
    X=model.vac.copy();X[-1]+=1e-4;X[2]+=2e-4;e=1e-4
    H=model.full_hessian(X)
    for k in [2,13,20,21,48]:
        v=np.eye(len(X))[k]*e;d=(model.potential(X+v)[1]-model.potential(X-v)[1])/(2*e)
        # quartic derivative central error is O(e^2).
        assert np.max(abs(d-H[:,k]))<5e-7

def test_third_tensor_and_full_matrix_derivatives(model):
    X=model.vac.copy();X[-1]+=2e-4;T=model.hessian_derivatives(X);e=1e-3
    assert np.max(abs(T-T.transpose(1,0,2)))<1e-7
    for k in [2,13,20,21,48]:
        v=np.eye(len(X))[k]*e;numeric=(model.full_hessian(X+v)-model.full_hessian(X-v))/(2*e)
        assert np.max(abs(numeric-T[k]))<1e-7

def test_classical_scaling_in_physical_coordinates(model):
    r=.003;X=model.vac/np.sqrt(r);e=.002
    def g(Y):return model.potential(np.sqrt(r)*Y)[1]/np.sqrt(r)
    for k in [2,20,48]:
        v=np.eye(len(X))[k]*e;column=(g(X+v)-g(X-v))/(2*e)
        assert np.max(abs(column-model.full_hessian(model.vac)[:,k]))<3e-7
    assert weak_continuation_certificate()==packet()['weak_continuation_theorem']

def test_complete_masses_and_loop_correction_scaling():
    for row in packet()['continuations']:
        assert row['maximum_tree_fermion_matrix_error']<1e-14
        assert row['maximum_scalar_Hessian_error']<1e-10
        assert row['maximum_mass_correction_scaling_error']<1e-14
        assert max(abs(x) for x in row['neutral_first_order_phases'])<1e-14

def test_angular_response_and_fermion_zero(model):
    T=model.angular_tangents();assert T.shape==(21,12)
    assert np.max(abs(T.T@T-np.eye(12)))<1e-12
    x=packet()['non_Gaussian_full_feedback'];assert x['isospectral_angular_scalar_force_norm']>1e-3
    assert x['isospectral_angular_fermion_force_norm']<1e-12
    assert max(c['absolute_error'] for c in x['angular_finite_difference_checks'])<3e-8
    assert abs(packet()['angular_force_extension_difference'])<1e-10

def test_local_stationary_branch_and_soft_spectrum(model):
    row=packet()['neutral_loop_stationary_branch'];X=np.array(row['rescaled_coordinates_Y'])
    F=model.potential(X)[1]+row['r']*model.loop_gradient(X)
    assert np.max(abs(F))<2e-10
    assert row['minimum_neutral_loop_Hessian_eigenvalue']>0
    assert row['relative_shift_over_full_background']<1e-5
    assert abs(row['conditional_canonical_tree_quartet_at_loop_vacuum'])>1e-4
    assert next(x for x in packet()['continuations'] if x['r']==.001)['minimum_bare_Hessian_at_linear_displacement']<0

def test_loop_Hessian_independent_direction(model):
    row=packet()['neutral_loop_stationary_branch'];X=np.array(row['rescaled_coordinates_Y']);v=np.zeros(len(X));v[2]=.4;v[13]=.5;v[48]=.2
    e=2e-7;direction=(model.loop_gradient(X+e*v)-model.loop_gradient(X-e*v))/(2*e)
    assert np.all(np.isfinite(direction))
    assert row['loop_Hessian_antisymmetric_residual']<1e-5
    assert np.max(abs(direction-model.loop_hessian(X)@v))<1e-3

def test_domain_rejections():
    with pytest.raises(ValueError):scalar_CW([[0.]])
    with pytest.raises(ValueError):scalar_CW([[1.]],mu=0)
    with pytest.raises(ValueError):scalar_CW([[1.,2.],[0.,1.]])
    with pytest.raises(ValueError):scalar_CW_gradient([[1.]],[[[float('nan')]]])
