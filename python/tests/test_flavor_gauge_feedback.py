import json
from pathlib import Path
import numpy as np
import pytest
from perfectpower.flavor_gauge_feedback import *
from perfectpower.flavor_scalar_feedback import SingletScalarModel
ROOT=Path(__file__).resolve().parents[2]

@pytest.fixture(scope='module')
def model():return SingletScalarModel(json.loads((ROOT/'receipts/m22_interactions/flavor_singlet_mediation.json').read_text())['singlet_finite_UV'])

def packet():return json.loads((ROOT/'receipts/m22_interactions/flavor_gauge_feedback.json').read_text())

def test_vector_multiplicities_and_subtraction():
    h=2.;mu=.8;g=.7;gp=.3
    w=g*g*h*h/4;z=(g*g+gp*gp)*h*h/4
    expected=(6*w*w*(np.log(w/mu**2)-5/6)+3*z*z*(np.log(z/mu**2)-5/6))/(64*np.pi**2)
    assert vector_CW(h,g,gp,mu)[0]==pytest.approx(expected,rel=1e-14)

def test_vector_derivatives_against_potential():
    h=2.3;e=1e-4
    v,d,k=vector_CW(h)
    assert d==pytest.approx((vector_CW(h+e)[0]-vector_CW(h-e)[0])/(2*e),rel=2e-8)
    assert k==pytest.approx((vector_CW(h+e)[1]-vector_CW(h-e)[1])/(2*e),rel=2e-8)

def test_fixed_coupling_physical_coordinate_pullback():
    h=.042;r=1e-6;e=1e-7
    v,d,k=pulled_vector_CW(h,r)
    physical=vector_CW(h/np.sqrt(r))
    assert v==pytest.approx(r*physical[0]);assert d==pytest.approx(np.sqrt(r)*physical[1]);assert k==physical[2]
    assert d==pytest.approx((pulled_vector_CW(h+e,r)[0]-pulled_vector_CW(h-e,r)[0])/(2*e),rel=1e-9)

def test_calibration_only_fits_tadpole_and_retains_curvature():
    h=.04;v,d,k,delta=calibrated_vector_CW(h,h)
    assert v==0 and d==0
    _,raw_d,raw_k=pulled_vector_CW(h)
    assert delta==pytest.approx(raw_d/h);assert k==pytest.approx(raw_k-delta)
    e=1e-5
    assert k==pytest.approx((calibrated_vector_CW(h+e,h)[1]-calibrated_vector_CW(h-e,h)[1])/(2*e),rel=1e-7)

def test_stable_near_reference_calibrated_tadpole():
    h=.04;step=1e-12
    _,d,k,_=calibrated_vector_CW(h+step,h)
    k0=calibrated_vector_CW(h,h)[2]
    assert d==pytest.approx(k0*step,rel=1e-5)

def test_symbolic_gauge_identities():assert exact_gauge_identities()==packet()['exact_identities']

def test_all_portals_are_isospectral_invariants(model):
    _,D=model.invariants(model.z);assert np.max(abs(D[:8]@model.angular_tangents()))<1e-12
    assert packet()['maximum_quadratic_portal_isospectral_derivative']<1e-12

def test_raw_gauge_limit_is_not_the_neutral_weak_limit():
    rows=packet()['raw_fixed_gauge_continuation'];weak=rows[-1]
    assert weak['relative_linear_shift']>100
    assert abs(weak['linear_Higgs_shift_over_reference'])>1e4
    assert weak['minimum_bare_Hessian_at_linear_displacement']<0
    assert all(x['direct_isospectral_angular_force_norm']==0 for x in rows)

def test_branch_recomputed_tadpoles_and_ward_identity(model):
    for p in packet()['tadpole_calibrated_hard_branches']:
        X=np.array(p['rescaled_coordinates_Y']);_,g=model.potential(X);F=g+p['r']*model.loop_gradient(X)
        _,d,k,delta=calibrated_vector_CW(X[20],model.vac[20],p['r']);F[20]+=d
        assert np.max(abs(F))<2e-10
        assert F[20]/X[20]==pytest.approx(p['Goldstone_Ward_residual'],abs=1e-11)
        assert abs(p['Goldstone_tree_plus_mass_adjustment_squared_mass']+p['Goldstone_hard_Ward_correction'])<1e-10
        assert p['minimum_bare_neutral_Hessian_eigenvalue']>0
        assert p['minimum_hard_potential_curvature_eigenvalue']>0
        assert p['vector_radial_curvature_over_reference_tree']>1e4
        assert abs(p['conditional_canonical_tree_quartet'])>1e-4

def test_hard_curvature_independent_Higgs_column(model):
    p=packet()['tadpole_calibrated_hard_branches'][0];X=np.array(p['rescaled_coordinates_Y']);r=p['r'];e=1e-8
    def gradient(Y):
        F=model.potential(Y)[1]+r*model.loop_gradient(Y);F[20]+=calibrated_vector_CW(Y[20],model.vac[20],r)[1];return F
    v=np.eye(len(X))[20]*e;numeric=(gradient(X+v)-gradient(X-v))/(2*e)
    H=model.full_hessian(X)+r*model.loop_hessian(X);H[20,20]+=calibrated_vector_CW(X[20],model.vac[20],r)[2]
    assert np.max(abs(numeric-H[:,20]))<1e-6

def test_domains_and_zero_limits():
    assert vector_CW(0.)==(0.,0.,0.)
    assert vector_CW(2.,g=0,gprime=0)==(0.,0.,0.)
    for kw in [{'mu':0},{'g':-1},{'h':float('nan')}]:
        args={'h':1.};args.update(kw)
        with pytest.raises(ValueError):vector_CW(**args)
    with pytest.raises(ValueError):pulled_vector_CW(.1,r=0)
    with pytest.raises(ValueError):calibrated_vector_CW(0.,.1)
    with pytest.raises(ValueError):calibrated_vector_CW(float('nan'),.1)
