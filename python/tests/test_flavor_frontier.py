"""Exact tensors, independent running identities and physical exclusions."""
from pathlib import Path
from fractions import Fraction
import json
import numpy as np
import pytest
from perfectpower.exact_nonet_algebra import *
from perfectpower.flavor_mechanism_search import *
from perfectpower.nonet_running import *
from perfectpower.nonet_physical_tests import *
from perfectpower.nonet_potential import joint_higgs,nonet_fields
from develop_valentiner_nonet_joint import hessian,frame_and_spectrum
from develop_flavor_frontier import callan_symanzik_check
from valentiner_adjoint_quartics import quartic_projectors,CP_odd_projector

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'receipts/m22_interactions'
SAVED=json.loads((OUT/'flavor_frontier.json').read_text())
SOURCE=json.loads((OUT/'valentiner_nonet_joint.json').read_text())
TABLE=json.loads((OUT/'nonet_scalar_loop_algebra.json').read_text())['nonzero_symmetric_products']
FULL=json.loads((OUT/'nonet_higgs_exact_loop_algebra.json').read_text())

@pytest.fixture(scope='module')
def tensors():
    P=np.array(quartic_projectors()[0]);Q,D,cert=certify_projectors(P)
    return P,Q,D,cert

@pytest.fixture(scope='module')
def kernel(tensors):
    A=np.zeros((61,61,61))
    for k,i,j,c in FULL['symmetric_products']:A[k,i,j]=A[k,j,i]=float(Fraction(c))
    return RunningKernel(tensors[0],A)

def test_exact_projectors_and_source_tensor_identities(tensors):
    P,Q,D,cert=tensors
    assert cert['ranks']==[1,8,8,9,10]
    result=verify_loop_table(exact_quartics(Q,D),TABLE)
    assert result['symmetric_products_verified']==1378
    assert result['exact_zero_residual_for_every_product']

def test_exact_Higgs_extension_and_independence(tensors):
    _,Q,D,_=tensors;polys=extended_quartics(Q,D)
    assert verify_loop_table(polys,FULL['symmetric_products'])==FULL['exact_tensor_proof']
    assert independence_witness(polys)['exact_rank']==61

def test_tampered_loop_coefficient_is_rejected(tensors):
    bad=[list(t) for t in TABLE];bad[0][3]=str(Fraction(bad[0][3])+Fraction(1,10**12))
    with pytest.raises(AssertionError):verify_loop_table(exact_quartics(tensors[1],tensors[2]),bad)

def test_exact_finite_current_eigenvalues(tensors):
    P,Q,D,_=tensors;answer=current_eigenvalues(Q,D,exact_quartics(Q,D))
    assert answer['finite8_self_current_eigenvalues']==['248/15','16/5','-112/15']
    numerical=finite_mediator_current_running([[.3,.04],[.2,-.03]],P)
    expected=16*np.array([.3,.2])[:,None]+np.array([.04,-.03])[:,None]*np.array([248/15,16/5,-112/15])
    assert np.max(abs(numerical-expected))<1e-10

def test_complete_coordinate_support_census():
    result=coordinate_subalgebra_census(TABLE)
    assert result==SAVED['coordinate_subalgebra_census']
    assert len(result['closed_supports'])==14
    assert all(len(row)==9 for row in result['closed_supports'] if set(row)&{48,49,50,51})

def test_exact_rotated_SU3_closure():
    u=np.zeros(52,int);u[49:52]=1
    result=exact_subalgebra(TABLE,[np.eye(52,dtype=int)[10].tolist(),np.eye(52,dtype=int)[22].tolist(),u.tolist()])
    assert result['dimension']==5

def test_mass_gap_symbolic_certificate_and_finite_spectra():
    assert pure_adjoint_mass_gap_certificate()==SAVED['pure_adjoint_complete_action']['mass_hierarchy_certificate']
    rng=np.random.default_rng(312)
    for _ in range(80):
        eig=rng.normal(size=3);eig-=np.mean(eig);a,M=np.exp(rng.uniform(-2,2,2))
        D=np.block([[a*np.eye(3),np.zeros((3,3))],[np.diag(eig),M*np.eye(3)]])
        m=np.sort(np.linalg.svd(D,compute_uv=False))[:3]
        assert m[1]/m[0]<1+m[1]/m[2]<2
        f=(a*a-m*m)*(M*M-m*m)/(m*m)
        assert np.allclose(np.sort(f),np.sort(eig*eig),rtol=1e-9,atol=1e-9)

def test_singlet_shift_changes_mass_gap_assumptions():
    # An explicit source trace permits a much stronger hierarchy.
    a=.03;C=np.diag([100.,1.,.01]);D=np.block([[a*np.eye(3),np.zeros((3,3))],[C,np.eye(3)]])
    m=np.sort(np.linalg.svd(D,compute_uv=False))[:3]
    assert m[1]/m[0]>50 and np.trace(C)!=0

def test_exact_CP_odd_operator_and_tree_mass_phase(tensors):
    _,Q,D,_=tensors;odd,proof=certify_odd_projector(CP_odd_projector(),Q,D)
    assert proof['exact_CP_parity']==-1 and proof['exact_group_invariant']
    saved=SAVED['dimension_eight_quality_operator'];v=saved['vacuum_value']
    for cutoff in [1,10,100,1000]:
        y=.57+1j*v/cutoff**4;matrix=np.block([[.03*y*np.eye(3),np.zeros((3,3))],[np.diag([1.,2.,3.]),np.eye(3)]])
        phase=np.angle(np.linalg.slogdet(matrix)[0])
        assert phase==pytest.approx(saved['example_phases'][str(cutoff)],abs=1e-16)

@pytest.mark.parametrize('seed',[3,7,11])
def test_tensor_Yukawa_running_matches_independent_formula(seed):
    rng=np.random.default_rng(seed);p=rng.normal(size=(2,4))*.5;g=rng.random(3)
    answer,gamma,cert=yukawa_beta(p,g)
    assert np.max(abs(answer-analytic_yukawa_beta(p,g)))<1e-11
    assert np.max(abs(gamma-scalar_gamma(p,g)))<1e-12

def test_universal_three_family_SM_Higgs_running(kernel):
    c=np.zeros(61);c[52]=.13;p=np.zeros((2,4));p[:,0]=[.9,.2];g=np.array([1.,.65,.36])
    result=kernel.beta(c,np.zeros(9),p,np.ones(2),g)
    trace=9*np.sum(p[:,0]**2)
    expected=24*c[52]**2+4*c[52]*(trace-9*g[1]**2/4-3*g[2]**2/4)-18*np.sum(p[:,0]**4)
    expected+=9*g[1]**4/8+3*g[1]**2*g[2]**2/4+3*g[2]**4/8
    assert result['quartics'][52]==pytest.approx(expected,abs=1e-11)

def test_box_polynomial_against_Weyl_mass_tensor(tensors):
    rng=np.random.default_rng(71);p=rng.normal(size=(2,4));Y=yukawa_tensors(p)
    for _ in range(4):
        z=rng.normal(size=24);M=np.einsum('a,aij->ij',z,Y);K=M.conj().T@M
        direct=-3*np.trace(K@K).real
        assert fermion_box(z,p)==pytest.approx(direct,rel=1e-12)
        assert quartic_value_gradient(z,tensors[0])[0]@fermion_box_coefficients(p)==pytest.approx(direct,rel=1e-12)

def test_scalar_mass_wave_maps_and_full_Callan_Symanzik(kernel,tensors):
    rng=np.random.default_rng(391);c=rng.normal(size=61)*.03;q=rng.normal(size=9)*.1
    p=rng.normal(size=(2,4))*.4;m=np.array([.8,1.3]);g=np.array([1.,.65,.36])
    answer=callan_symanzik_check(kernel,c,q,p,m,g,tensors[0])
    assert max(answer['off_grid_relative_residuals'])<1e-11

def test_current_relations_split_under_finite_anisotropy():
    result=mediation_beta([.2,.2],[.05,.05],[.01,.01,.01],np.ones(3),np.ones(3),np.ones(3)*9,['248/15','16/5','-112/15'])
    assert np.ptp(result['beta_exchange'])>.2
    symmetric=mediation_beta([.2,.2],[0,0],[.01,.01,.01],np.ones(3),np.ones(3),np.ones(3)*9,['248/15','16/5','-112/15'])
    assert np.ptp(symmetric['beta_exchange'])==0

def test_gauge_running_and_heavy_threshold_sign():
    g=np.array([1.,.65,.36]);assert gauge_beta(g)==pytest.approx(np.array([-3,-19/6,27/2])*g**3)
    assert np.max(abs(gauge_threshold_delta_inverse(g,np.ones((2,3))*2,2)))==0
    d=gauge_threshold_delta_inverse(g,np.ones((2,3))*np.e,1)
    assert d==pytest.approx(-np.array([4,0,20/3])/(8*np.pi*np.pi))
    with pytest.raises(ValueError):gauge_threshold_delta_inverse(g,np.zeros((2,3)),1)

def test_exact_heavy_scalar_spectral_matching():
    cert=heavy_scalar_matching_certificate();assert cert==SAVED['heavy_scalar_matching_certificate']
    M,a,d=3.,.7,.6
    def heavy(t):
        H=np.array([[a*t*t+d*d*t*t/M**2,d*t],[d*t,M*M]])
        w=np.linalg.eigvalsh(H)[1];return (w*w*(np.log(w/M**2)-1.5)+1.5*M**4)/4
    for t in [.1,.05]:
        prediction=-d*d*t*t/2-a*d*d*t**4/(2*M*M)
        assert abs(heavy(t)-prediction)<2e-3*t**6+2e-14

def test_actual_finite_mass_kinetic_response_rank():
    z=np.array(SOURCE['canonical_coordinates']);answer=kinetic_response(z)
    assert answer['row_normalized_response_singular_values'][-1]>.19
    assert answer['nine_word_determinant']==pytest.approx(answer['8_chi_cubed'],rel=1e-8)
    for sides in answer['finite_checks']:
        for side in sides:
            assert side['maximum_light_mass_change']<1e-12 and side['metric_minimum']>.99
            assert abs(side['tree_phase'])<1e-12

def test_lower_CP_conserving_competitor_full_action(tensors):
    row=SAVED['vacuum_comparison']['stable_CP_conserving_competitor'];z=np.array(row['coordinates'])
    c=np.array(SOURCE['coefficients']);portals=np.array(SOURCE['Higgs_portals']);P=tensors[0]
    fun=lambda z:joint_higgs(z,c,P,portals,SOURCE['Higgs_mu2'])
    energy,gradient=fun(z);baseline=fun(np.array(SOURCE['canonical_coordinates']))[0]
    assert baseline-energy>.014 and np.linalg.norm(gradient)<1e-8
    assert np.linalg.eigvalsh(hessian(fun,z))[0]>4e-4
    assert abs(frame_and_spectrum(z)[0]['J'])<1e-12

def test_high_temperature_Higgs_normalization(tensors):
    c=np.zeros(61);c[52]=.13;p=np.zeros((2,4));p[:,0]=[.9,.2];g=np.array([1.,.65,.36])
    z=np.zeros(24);z[22]=1
    expected=.13/4+3*np.sum(p[:,0]**2)/8+(3*g[1]**2+g[2]**2)/32
    assert thermal_quadratic(z,c,tensors[0],p,g)==pytest.approx(expected,abs=1e-12)

def test_running_records_boundary_and_quality_scopes():
    running=SAVED['complete_soft_running'];assert running['nonconstant_parameters']==92
    for row in running['trajectory']:assert row['singlet_Yukawa_ratios']==pytest.approx([1/7,1/7],abs=1e-12)
    assert running['first_Higgs_quartic_zero_log_scale']>.5
    assert SAVED['quantum_vacuum_feedback']['shift_over_background_norm']>10
    assert min(SAVED['leading_high_temperature_mass_eigenvalues'])>.99
