"""Finite scalar residue matching and the precise phase-protection boundary."""
from pathlib import Path
import json
import numpy as np
import pytest
from perfectpower.nonet_spectral_matching import *
from perfectpower.flavor_resummed_phase import *
from perfectpower.flavor_quantum import scalar_threshold
from perfectpower.nonet_running import fermion_box_coefficients,RunningKernel
from valentiner_adjoint_quartics import quartic_projectors

ROOT=Path(__file__).resolve().parents[2]

def test_exact_gaussian_determinant_and_residue_identities():
    answer=exact_gaussian_spectral_certificate()
    assert answer['exact_one_source_identity'] and answer['exact_unequal_three_mediator_polynomial_identity']

def test_exact_gaussian_wall_bound_agrees_with_independent_BigInt_bridge():
    p=exact_gaussian_wall_certificate();assert p['example_upper_squared']=='3952/3645'
    bridge=json.loads((ROOT/'receipts/flavor_cosmology/gaussian_wall_bridge.json').read_text())
    assert bridge['rigorous_tension_upper_squared']==p['example_upper_squared']
    assert bridge['rigorous_tension_lower_squared']==p['example_lower_squared']

@pytest.mark.parametrize('seed',[12,20,32])
def test_unequal_mediator_poles_bounds_and_residues(seed):
    rng=np.random.default_rng(seed);n,k=4,6;X=rng.normal(size=(n,n));H=X.T@X+.3*np.eye(n)
    D=rng.normal(size=(k,n));M2=np.linspace(40,80,k);answer=finite_scalar_poles(H,D,M2)
    exact=np.array(answer['exact_light_poles_squared']);local=np.array(answer['two_derivative_EFT_masses_squared']);bare=np.array(answer['bare_source_masses_squared'])
    assert answer['light_pole_maximum_absolute_error']<1e-11
    assert answer['full_light_subspace_projector_error']<1e-11
    assert answer['full_norm_residual']<1e-12 and answer['full_orthogonality_residual']<1e-10
    assert np.all(exact<=local+1e-11) and np.all(local<=bare+1e-11)
    assert np.all(np.array(answer['rigorous_ordered_lower_bounds'])<=exact+1e-11)
    for z in exact:
        step=1e-4
        derivative=-(effective_pencil(H,D,M2,z+step)-effective_pencil(H,D,M2,z-step))/(2*step)
        assert np.max(abs(derivative-residue_metric(D,M2,z)))<1e-9

def test_zero_currents_and_degenerate_source_spectrum():
    H=np.eye(3);D=np.zeros((2,3));answer=finite_scalar_poles(H,D,[10,20])
    assert answer['exact_light_poles_squared']==pytest.approx([1,1,1])
    assert answer['full_orthogonality_residual']<1e-12 and answer['source_pole_weights']==pytest.approx([1,1,1])

def test_pole_preconditions_and_positive_tree_metric():
    D=np.array([[1.,2.],[3.,4.]])
    assert min(np.linalg.eigvalsh(tree_metric(D,[3,5])))>1
    with pytest.raises(ValueError):finite_scalar_poles(np.eye(2)*6,D,[3,5])
    with pytest.raises(ValueError):finite_scalar_poles(-np.eye(2),D,[3,5])
    with pytest.raises(ValueError):full_hessian(np.eye(2),D,[0,5])
    with pytest.raises(ValueError):effective_pencil(np.eye(2),D,[3,5],3)

def test_actual_48_and_76_scalar_matching_receipt():
    saved=json.loads((ROOT/'receipts/m22_interactions/flavor_spectral_matching.json').read_text())
    for name,n in [('finite27',48),('universal55',76)]:
        row=saved['finite_scalar_matching'][name]
        assert len(row['full_UV_masses_squared'])==n and row['light_pole_maximum_absolute_error']<1e-10
        assert row['cross_sector_kinetic_block_norm']>3e-4
        assert row['maximum_two_derivative_relative_pole_error']<1e-4

def test_exact_resolvent_higher_phase_counterexample():
    p=exact_resolvent_phase_certificate();assert p['resolvent_first_order_phase']=='0'
    assert p['resolvent_quadratic_phase_coefficient']=='-5152/727803505'

def test_B0_threshold_matches_80_digit_direct_top_block():
    p=spectral_phase_example();q=high_precision_B0_top_block(80)
    assert abs(p['first_order_phase'])<1e-18 and p['relative_correction_norm']<.001
    assert p['quadratic_determinant_phase']==pytest.approx(float(q['quadratic_determinant_phase']),abs=1e-20)
    assert p['resummed_phase']==pytest.approx(float(q['resummed_phase']),abs=1e-20)
    assert abs(p['resummed_phase'])>4e-10
    for row in p['formal_scaling']:
        t=row['formal_loop_multiplier'];assert row['determinant_phase']/t**2==pytest.approx(p['quadratic_determinant_phase'],rel=.0005)

def test_structured_portal_row_still_has_higher_determinant_phase():
    p=spectral_phase_example(True);H=p['scalar_Hessian']
    assert H[0,2]==H[0,3]==0 and H[0,1]!=0
    assert min(p['positive_scalar_eigenvalues'])>.2 and abs(p['first_order_phase'])<1e-16
    assert abs(p['resummed_phase'])>1e-10 and p['relative_correction_norm']<.02

def test_sequestered_Higgs_keeps_resummed_matrix_real():
    p=spectral_phase_example();H=p['scalar_Hessian'].copy();H[0,1:]=H[1:,0]=0
    q=scalar_threshold(p['D'],p['vertices'],H)
    assert abs(q['resummed_one_loop_matrix_phase'])<1e-18
    assert q['relative_correction_norm']<1

def test_portals_regenerate_when_Higgs_and_sources_both_couple():
    p=np.array([[.8,.1,.7,.5],[.4,.2,.6,.3]]);box=fermion_box_coefficients(p)
    for f,(y,e,s,a) in enumerate(p):
        assert box[53+4*f:57+4*f]==pytest.approx(-12*y*y*np.array([3*e*e,3*s*s,6*e*s,a*a]))
    cert=Higgs_sequestering_certificate();assert cert['source_Higgs_portal_beta_at_zero_portals']==['-36*e**2*y**2','-36*t**2*y**2','-72*e*t*y**2','-12*a**2*y**2']
    from fractions import Fraction
    table=json.loads((ROOT/'receipts/m22_interactions/nonet_higgs_exact_loop_algebra.json').read_text());A=np.zeros((61,61,61))
    for k,i,j,value in table['symmetric_products']:A[k,i,j]=A[k,j,i]=float(Fraction(value))
    kernel=RunningKernel(np.array(quartic_projectors()[0]),A);c=np.zeros(61);c[:52]=np.linspace(.001,.01,52);c[52]=.13
    result=kernel.beta(c,np.zeros(9),p,np.ones(2),np.array([1,.65,.36]))
    assert result['quartics'][53:]==pytest.approx(box[53:],abs=1e-12)
