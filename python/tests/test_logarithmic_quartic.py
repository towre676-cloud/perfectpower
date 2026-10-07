import json,math
from pathlib import Path
import numpy as np
import pytest
from perfectpower.logarithmic_quartic import *
from perfectpower.flavor_scalar_feedback import SingletScalarModel
from perfectpower.flavor_gauge_feedback import calibrated_vector_CW
ROOT=Path(__file__).resolve().parents[2]

@pytest.fixture(scope='module')
def model():return SingletScalarModel(json.loads((ROOT/'receipts/m22_interactions/flavor_singlet_mediation.json').read_text())['singlet_finite_UV'])

def packet():return json.loads((ROOT/'receipts/m22_interactions/flavor_radial_profile.json').read_text())

def test_complete_seven_phase_classes():
    phases=['origin_only','fold','broken_metastable','coexistence','origin_metastable','origin_spinodal','broken_only']
    for value,phase in zip([-1.,'fold',-.34,'coexistence',-.1,'origin',.1],phases):
        p=LogQuartic(1.,1.,value).classify();assert p['phase']==phase
        assert len(p['stationary_points'])==({'origin_only':1,'fold':3,'broken_metastable':5,'coexistence':5,'origin_metastable':5,'origin_spinodal':3,'broken_only':3}[phase])

def test_all_real_stationary_points_and_energy_formula():
    for eta in [-1.,'fold',-.34,'coexistence',-.1,0.,.1,500.,1e100]:
        q=LogQuartic(.7,1.3,eta)
        for p in q.classify()['stationary_points']:
            v,d,k=q.evaluate(p['h'])
            assert abs(d)<2e-13*max(1,abs(p['h'])**3)
            assert v==pytest.approx(p['energy'],rel=5e-13,abs=1e-15)
            assert k==pytest.approx(p['curvature'],rel=5e-13,abs=1e-14)

def test_potential_derivatives_and_evenness():
    q=LogQuartic(.8,.6,-.1);h=.9;e=1e-5
    v,d,k=q.evaluate(h);assert q.evaluate(-h)==pytest.approx((v,-d,k))
    assert d==pytest.approx((q.evaluate(h+e)[0]-q.evaluate(h-e)[0])/(2*e),rel=1e-8)
    assert k==pytest.approx((q.evaluate(h+e)[1]-q.evaluate(h-e)[1])/(2*e),rel=1e-8)

def test_global_radial_minima_and_barriers():
    for eta in [-.34,'coexistence',-.1,.2]:
        q=LogQuartic(1.,1.,eta);p=q.classify();ground=min(q.evaluate(h)[0] for h in p['global_radial_minima'])
        assert all(q.evaluate(h)[0]>=ground-1e-14 for h in np.linspace(-3,3,301))
        if p['barriers']:assert min(p['barriers'].values())>0
    p=LogQuartic(1.,1.,'coexistence').classify();assert len(p['global_radial_minima'])==3
    assert next(x['y'] for x in p['stationary_points'] if x['branch']=='W0')==pytest.approx(math.exp(-.5))

def test_implicit_control_response_and_fold_divergence():
    eta=-.2;e=1e-6;q=LogQuartic(.7,1.3,eta);r=q.control_response()
    hplus=LogQuartic(.7,1.3,eta+e).minimum_positive_radius();hminus=LogQuartic(.7,1.3,eta-e).minimum_positive_radius()
    assert r['dh_deta']==pytest.approx((hplus-hminus)/(2*e),rel=1e-8)
    near=LogQuartic(1.,1.,-1/math.e+1e-10).control_response()['dy_deta'];assert near>1e4

def test_compiler_matches_full_mediator_tree_and_vector_slice(model):
    X=model.vac.copy();X[2]+=2e-4;X[-1]+=1e-4
    q,c=compile_vector_radial(model,X);Y=X.copy();Y[20]=0.;constant=model.potential(Y)[0]
    # The calibrated vector API sets its zero at h0, while the normal form
    # sets its zero at h=0. Differences cancel this arbitrary additive choice.
    h0=model.vac[20]
    def energy(h):
        Y=X.copy();Y[20]=h;return model.potential(Y)[0]+calibrated_vector_CW(h,h0)[0]
    for h in [.025,.04,.065]:
        Y=X.copy();Y[20]=h
        assert q.evaluate(h)[1]==pytest.approx(model.potential(Y)[1][20]+calibrated_vector_CW(h,h0)[1],abs=2e-13)
        assert q.evaluate(h)[0]-q.evaluate(h0)[0]==pytest.approx(energy(h)-energy(h0),abs=2e-14)

def test_profile_hessian_congruence_and_inertia():
    rng=np.random.default_rng(712);Q=rng.normal(size=(7,7));H=(Q+Q.T)/2;H[3,3]=2.
    S,response=profile_hessian(H,3);ix=[i for i in range(7) if i!=3];L=np.eye(7);L[3,ix]=response;D=L.T@H@L
    assert np.max(abs(D[3,ix]))<1e-14
    assert np.max(abs(D[np.ix_(ix,ix)]-S))<1e-14
    assert np.sum(np.linalg.eigvalsh(H)<0)==np.sum(np.linalg.eigvalsh(S)<0)

def test_radial_stiffening_is_positive_rank_one():
    rng=np.random.default_rng(29);Q=rng.normal(size=(6,6));H=Q.T@Q+np.eye(6);k=7.;K=H.copy();K[2,2]+=k
    S0,_=profile_hessian(H,2);S1,_=profile_hessian(K,2);ix=[i for i in range(6) if i!=2];b=H[ix,2];c=H[2,2]
    assert np.max(abs(S1-S0-k*np.outer(b,b)/(c*(c+k))))<1e-13
    w=np.linalg.eigvalsh(S1-S0);assert w[0]>-1e-13 and np.sum(w>1e-10)==1

def test_profiled_solver_and_49_coordinate_agreement(model):
    p=packet()['profiled_hard_branch'];X=np.array(p['rescaled_coordinates_Y']);F=model.potential(X)[1]+p['r']*model.loop_gradient(X)
    F[20]+=calibrated_vector_CW(X[20],model.vac[20],p['r'])[1]
    assert np.max(abs(F))<2e-13
    assert p['minimum_profiled_48_curvature_eigenvalue']>0
    assert packet()['maximum_profiled_vs_full_solver_coordinate_difference']<1e-10
    assert packet()['full_hard_background_profile']['rank_one_stiffening_identity_error']<1e-12

def test_profiled_radial_response_against_nonlinear_minimization(model):
    q,c=compile_vector_radial(model,model.vac);X=model.vac.copy();X[20]=q.minimum_positive_radius()
    H=model.full_hessian(X);H[20,20]+=calibrated_vector_CW(X[20],model.vac[20])[2];_,response=profile_hessian(H);ix=[i for i in range(len(X)) if i!=20];e=1e-5
    for k in [2,13,48]:
        v=np.eye(len(X))[k]*e
        plus=compile_vector_radial(model,X+v)[0].minimum_positive_radius();minus=compile_vector_radial(model,X-v)[0].minimum_positive_radius()
        assert response[ix.index(k)]==pytest.approx((plus-minus)/(2*e),rel=1e-5,abs=1e-11)

def test_exact_identities_and_domain_boundaries():
    assert exact_radial_identities()==packet()['exact_identities']
    for args in [(0.,1.,0.),(1.,0.,0.),(1.,1.,float('nan')),(1.,1.,'unknown')]:
        with pytest.raises(ValueError):LogQuartic(*args)
    with pytest.raises(ValueError):profile_hessian([[0.]])
    with pytest.raises(ValueError):LogQuartic(1.,1.,'fold').minimum_positive_radius()
