import json
from pathlib import Path
import numpy as np
import unittest
from scipy.integrate import quad
from perfectpower.flavor_quantum import b0_finite,scalar_threshold,fermion_coleman_weinberg,fermion_CW_gradient
from valentiner_electroweak import vertices,scaled_kernel,COORDINATE_SCALES,norm_data
from develop_valentiner_canonical import fields
from valentiner_higher_operators import census
from perfectpower.flavor_canonical import full_spectrum,current_pair,pole_certificate

ROOT=Path(__file__).resolve().parents[2]
R=json.loads((ROOT/'receipts/m22_interactions/valentiner_quantum.json').read_text())
W=np.array(R['selected_field_coordinates']);F=fields(W)


def test_B0_equal_extreme_and_quadrature():
    for x,y in [(2.,2.),(2.,2.00001),(1e-30,100.),(100.,1e-30),(.2,3.)]:
        exact=-quad(lambda t:np.log(t*x+(1-t)*y),0,1,epsabs=1e-11)[0]
        assert abs(float(b0_finite(x,y))-exact)<1e-9
    assert np.isfinite(b0_finite(1e-100,100.))


def test_threshold_CP_and_real_couplings():
    rng=np.random.default_rng(7160);D=np.diag([.2,1.3,2.]);G=rng.normal(size=(4,3,3))+1j*rng.normal(size=(4,3,3))
    H=np.diag([.4,1.,3.,9.]);r=scalar_threshold(D,G,H)
    assert abs(r['delta_theta'])>1e-6
    assert abs(r['delta_theta']+scalar_threshold(D.conj(),G.conj(),H)['delta_theta'])<1e-14
    assert abs(scalar_threshold(D,G.real,H)['delta_theta'])<1e-14


def test_threshold_independent_of_fermion_and_scalar_basis():
    rng=np.random.default_rng(7133)
    unit=lambda:np.linalg.qr(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)))[0]
    D=np.diag([.2,1.3,2.]);G=rng.normal(size=(4,3,3))+1j*rng.normal(size=(4,3,3));H=np.diag([.4,1.,3.,9.])
    U,V=unit(),unit();O=np.linalg.qr(rng.normal(size=(4,4)))[0]
    transformed=np.einsum('ab,aij->bij',O,np.einsum('ij,ajk,kl->ail',U.conj().T,G,V))
    a=scalar_threshold(D,G,H);b=scalar_threshold(U.conj().T@D@V,transformed,O.T@H@O)
    assert abs(a['delta_theta']-b['delta_theta'])<1e-12


def test_CW_gradient_independently_by_finite_difference():
    rng=np.random.default_rng(7144);D=np.diag([.2,1.3,2.]).astype(complex)
    G=rng.normal(size=(5,3,3))+1j*rng.normal(size=(5,3,3));g=fermion_CW_gradient(D,G)
    for i in range(5):
        h=1e-6;numeric=(fermion_coleman_weinberg(D+h*G[i])-fermion_coleman_weinberg(D-h*G[i]))/(2*h)
        assert abs(g[i]-numeric)<1e-8


def test_all_70_flavor_vertices_are_actual_mass_derivatives():
    for sector in ['up','down']:
        G=vertices(sector);step=1e-6
        for i in range(70):
            e=np.eye(70)[i]*step/COORDINATE_SCALES[i]
            plus=full_spectrum(scaled_kernel(fields(W+e),sector),.03)['mass_matrix']
            minus=full_spectrum(scaled_kernel(fields(W-e),sector),.03)['mass_matrix']
            assert np.max(abs((plus-minus)/(2*step)-G[i]))<1e-9


def test_portal_norm_gradient_in_physical_coordinates():
    n,J=norm_data(W);rng=np.random.default_rng(7100);e=rng.normal(size=70);h=1e-6
    assert np.max(abs((norm_data(W+h*e)[0]-norm_data(W-h*e)[0])/(2*h)-J@e))<1e-9


def test_joint_branch_all_71_directions_positive():
    for r in R['joint_branch_scan']:
        assert r['joint_vacuum']['minimum_71_scalar_mass_squared']>0
        assert r['joint_vacuum']['stationarity_scaled_max']<1e-7
        assert abs(r['weak_CP_quartet'])>1e-7


def test_CP_partner_and_high_precision_trace():
    selected=R['joint_branch_scan'][-1]
    assert abs(selected['combined_scalar_delta_theta'])<1e-10
    assert R['selected_CP_partner']['opposite_phase_absolute_error']<5e-15
    assert abs(selected['weak_CP_quartet']+R['selected_CP_partner']['weak_CP_quartet'])<1e-12
    for high,low in zip(R['scalar_threshold_60_digit_trace_checks'],selected['scalar_threshold_by_sector']):
        assert abs(float(high)-low['delta_theta'])<1e-16
        assert abs(low['UV_phase_coefficient'])<1e-14


def test_spurion_scales_full_masses_and_retains_finite_currents():
    base=[full_spectrum(scaled_kernel(F,s),.03) for s in ['up','down']]
    scaled=[full_spectrum(scaled_kernel(F,s,1e-5),3e-7) for s in ['up','down']]
    assert np.max(abs(abs(current_pair(*base)['V'])-abs(current_pair(*scaled)['V'])))<1e-9
    for s,a,b in zip(['up','down'],base,scaled):
        assert np.max(abs(b['masses']/a['masses']/1e-5-1))<1e-12
        assert max(pole_certificate(scaled_kernel(F,s,1e-5),b,3e-7)['normalized_Schur_residuals'])<1e-12


def test_spurion_charge_selection_and_CW_scaling():
    c=R['spurion_selection']['new_Z6_charges']
    assert (-c['heavy_left']+c['heavy_right']+c['epsilon'])%6==0
    assert (-c['heavy_left']+c['bare_quarks']-c['epsilon'])%6==0
    assert (-c['bare_quarks']+c['heavy_right']+2*c['epsilon'])%6==0
    b=R['fermion_vacuum_backreaction']
    assert abs(b['CW_scale_ratio']/b['expected_ratio']-1)<1e-12
    assert b['maximum_linearized_flavor_coordinate_shift']<1e-10


def test_Goldstone_and_gauge_diagonal_phase_factors_real():
    # Full 12-state currents, before restriction to the three light modes.
    up,down=[full_spectrum(scaled_kernel(F,s),.03) for s in ['up','down']]
    V=up['left'][:3].conj().T@down['left'][:3]
    for spectrum in [up,down]:
        Z=spectrum['left'][:3].conj().T@spectrum['left'][:3]
        m=spectrum['masses'];G=1j*Z*m[None,:]/(np.sqrt(2)*.03)
        factors=np.einsum('ik,k,ki,i->ik',G,m,G,1/m)
        assert np.max(abs(factors.imag))<1e-13
        assert np.max(abs(np.diag(Z).imag))<1e-13
    # Charged Goldstone terms reduce to |V_ij|² m_j² / v².
    left=V*down['masses'][None,:]/.03
    right=up['masses'][:,None]*V/.03
    factors=left*right.conj()*down['masses'][None,:]/up['masses'][:,None]
    assert np.max(abs(factors.imag))<1e-13


def test_complete_exact_scalar_insertion_counts():
    c=census();saved=R['higher_fermion_operator_census']
    assert c==saved
    assert c['Higgs_covariant_counts_by_degree']==[1,2,9,21]
    assert c['heavy_mass_covariant_counts_by_degree']==[3,6,29,85]
    assert sum(row['multiplicity'] for row in c['covariants'])==156
    # Explicitly retain the finite-group channels missed by SU(3) trace words.
    assert any(row['fields']=={'S':2,'S-dagger':1} and row['multiplicity']==8 for row in c['covariants'])


def test_uniform_finite_EFT_quality_bound():
    q=R['finite_EFT_quality_bounds']
    assert all(q[i+1]['combined_absolute_phase_bound']<q[i]['combined_absolute_phase_bound'] for i in range(len(q)-1))
    assert q[-1]['combined_absolute_phase_bound']<1e-10
    for row in q:
        assert all(s['relative_operator_norm_bound']<1 for s in row['sectors'])


def test_hierarchical_inverse_matching_and_positive_polynomial_metrics():
    r=R['hierarchical_inverse_matching'];assert r['CKM_magnitude_error']<1e-10
    assert abs(r['matched_observables']['J'])>3e-5
    for row,actual in zip(r['sectors'],r['matched_observables']['spectra']):
        assert row['minimum_bare_metric_eigenvalue']>.5
        assert row['target_H_error_90_digits']<1e-65
        assert row['positive_completion_error_90_digits']<1e-55
        assert np.max(abs(np.array(actual)/np.array(row['target_Yukawa_eigenvalues'])-1))<1e-10


def test_invalid_loop_spectrum_and_spurion_rejected():
    for fun in [lambda:scalar_threshold(np.eye(2),np.ones((1,2,2)),np.array([[-1.]])),
                lambda:b0_finite(0,1),lambda:scaled_kernel(F,'up',0)]:
        try:fun()
        except ValueError:pass
        else:raise AssertionError('Expected ValueError')


if __name__=='__main__':
    suite=unittest.TestSuite(unittest.FunctionTestCase(f) for n,f in sorted(globals().items()) if n.startswith('test_'))
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(not result.wasSuccessful())
