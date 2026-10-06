"""Independent spectral, current, determinant and operator checks."""
from pathlib import Path
import sys,json,unittest
import numpy as np
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'python'))
from perfectpower.flavor_canonical import *
from develop_valentiner_canonical import fields,old_kernel,decoupling,legacy_determinant_certificate
from valentiner_canonical_quarks import match,PARAMETERS
from valentiner_canonical_operators import certificate
from develop_valentiner_adjoint_uv import cp_transform

R=json.loads((ROOT/'receipts/m22_interactions/valentiner_canonical.json').read_text())
OLD=json.loads((ROOT/'receipts/m22_interactions/valentiner_adjoint_uv.json').read_text())
W=np.array(OLD['vacuum']['field_coordinates']);F=fields(W)
K=[match(*F,s) for s in ['up','down']]


def test_exact_renormalizable_fermion_census():
    r=certificate();assert r['independent_real_renormalizable_coefficients']==10
    assert r['Higgs_right_fields']==['bare']
    assert r['exact_character_multiplicities']=={'triplet_endomorphism':1,'adjoint_singlet':0,'triplet_adjoint_triplet':1}
    assert {(t['left'],t['right'],t['scalar']) for t in r['mass_and_source_contractions']}=={
        ('D','D','identity'),('H_A','H_A','identity'),('H_B','H_B','identity'),
        ('D','bare','L-dagger'),('H_A','bare','A-dagger'),
        ('D','H_B','B'),('H_B','D','B-dagger'),('H_A','H_B','S'),('H_B','H_A','S-dagger')}


def test_same_adjoint_and_source_vacuum_used():
    L,A,B,S=F
    for sector,k in zip(['up','down'],K):
        p=PARAMETERS[sector]
        assert np.max(abs(k['M'][3:6,6:]-p[5]*S))<1e-15
        assert np.max(abs(k['M'][6:,3:6]-p[6]*dagger(S)))<1e-15
        assert np.max(abs(k['C'][:3]-p[7]*dagger(L)))<1e-15
        assert np.max(abs(k['C'][3:6]-p[8]*dagger(A)))<1e-15


def test_Hermitian_similarity_and_positive_determinants():
    for k in K:
        H=k['hermitian_similarity'];assert np.max(abs(H-dagger(H)))<1e-14
        assert np.linalg.eigvalsh(H)[0]>.7
        assert abs(np.angle(np.linalg.slogdet(k['M'])[0]))<1e-14


def test_exact_null_frame_and_canonical_metric():
    for k in K:
        E=k['null_frame'];assert np.max(abs(k['F']@E))<1e-13
        assert np.max(abs(dagger(E)@E-np.eye(3)))<1e-13
        assert np.max(abs(k['Y']-dagger(k['Y'])))<1e-13
        assert np.linalg.eigvalsh(k['Y'])[0]>.5


def test_six_nonzero_light_masses_and_nine_heavy_modes_each():
    for k in K:
        s=full_spectrum(k,.03)['masses'];assert len(s)==12
        assert min(s[:3])>.01 and s[3]>.7


def test_full_determinant_real_for_random_CP_breaking_sources():
    rng=np.random.default_rng(2030106)
    for _ in range(12):
        f=[.02*(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3))) for _ in range(4)]
        f[-1]-=np.trace(f[-1])/3*np.eye(3)
        for sector in ['up','down']:
            k=match(*f,sector);s=full_spectrum(k,.17);sign,logabs=np.linalg.slogdet(s['mass_matrix'])
            assert abs(sign-1)<1e-12
            assert abs(logabs-(3*np.log(.17*k['bare_y'])+np.linalg.slogdet(k['M'])[1]))<1e-12


def test_legacy_determinant_obstruction_reduced_independently():
    k=[old_kernel(F,s) for s in ['up','down']];r=legacy_determinant_certificate(F,k)
    assert abs(r['combined_strong_phase_at_theta_QCD_zero']+2.462637645511)<1e-9
    assert max(r['reduced_six_by_six_relative_errors'])<1e-9


def test_canonical_positive_metrics_preserve_full_determinant_phase():
    rng=np.random.default_rng(99012)
    for k in K:
        D=full_spectrum(k,.03)['mass_matrix'];phases=[]
        for _ in range(4):
            X=rng.normal(size=(12,12))+1j*rng.normal(size=(12,12));B=dagger(X)@X+np.eye(12)
            val,U=np.linalg.eigh(B);R=(U/np.sqrt(val))@dagger(U)
            phases.append(np.angle(np.linalg.slogdet(R@D@R)[0]))
        assert max(abs(p) for p in phases)<1e-12


def test_physical_weak_CP_and_opposite_partner():
    r=decoupling(K);p=decoupling([match(*fields(cp_transform(W)),s) for s in ['up','down']])
    assert abs(r['J'])>1e-7
    assert abs(r['J']+p['J'])<1e-12
    assert np.max(abs(np.array(r['abs_CKM'])-np.array(p['abs_CKM'])))<1e-10


def test_exact_scale_independent_frames_and_canonical_mass_formula():
    for sector,k in zip(['up','down'],K):
        singular=np.linalg.svd(np.linalg.solve(k['M'],k['C']),compute_uv=False)
        for scale in [.01,.0001]:
            q=match(*F,sector,mass_scale=scale)
            actual=np.linalg.svd(q['Y'],compute_uv=False)[::-1]
            expected=k['bare_y']*scale/np.sqrt(scale**2+singular**2)
            assert np.max(abs(actual/expected-1))<1e-9
    assert R['scale_scan_mixing_magnitude_residual']<1e-9


def test_positive_left_pole_metric_and_Schur_equation():
    for k in K:
        assert np.linalg.eigvalsh(k['Z1'])[0]>0
        p=pole_certificate(k,full_spectrum(k,.1),.1)
        assert max(p['normalized_Schur_residuals'])<1e-12
        assert max(p['pole_metric_norm_errors'])<1e-12


def test_positive_weak_current_deficits_and_exact_decomposition():
    s=[full_spectrum(k,.3) for k in K];c=current_pair(*s)
    for name in ['row','column']:
        assert np.linalg.eigvalsh(c[name+'_deficit'])[0]>0
        assert np.max(abs(c[name+'_deficit']-sum(c[name+'_positive_parts'])))<1e-13
        assert min(np.linalg.eigvalsh(p)[0] for p in c[name+'_positive_parts'])>-1e-13


def test_full_currents_are_rank_three_partial_isometries():
    su,sd=[full_spectrum(k,.3) for k in K];U,D=su['left'][:3],sd['left'][:3];V=dagger(U)@D
    Pu,Pd=dagger(U)@U,dagger(D)@D
    assert np.max(abs(V@dagger(V)-Pu))<1e-13
    assert np.max(abs(dagger(V)@V-Pd))<1e-13
    assert np.max(abs(Pu@Pu-Pu))<1e-13 and abs(np.trace(Pu)-3)<1e-13


def test_exact_Higgs_neutral_current_relation_and_mass_derivative():
    v=.1;step=1e-5
    for k in K:
        s=full_spectrum(k,v);h=higgs_coupling(s,k['T']);nc=dagger(s['left'][:3])@s['left'][:3]
        assert np.max(abs(h-nc*s['masses'][None,:]/v))<1e-12
        derivative=(full_spectrum(k,v+step)['masses']-full_spectrum(k,v-step)['masses'])/(2*step)
        assert np.max(abs(derivative-np.diag(h).real))<1e-8


def test_dimension_six_approximation_has_fourth_order_error():
    errors=[]
    for v in [.03,.1]:
        exact=current_pair(*[full_spectrum(k,v) for k in K]);approx=current_pair(*[dimension_six(k,v) for k in K])
        errors.append(np.max(abs(abs(exact['V'])-abs(approx['V']))))
    assert 115<errors[1]/errors[0]<130


def test_eighty_digit_independent_mass_and_CP_check():
    check=R['NB_80_digit_check'];record=R['NB_finite_scans'][3]
    assert abs(float(check['full_determinant_phase']))<1e-18
    assert max(abs(float(v)) for v in R['NB_exact_decimal_determinants']['heavy_determinant_phases'])<1e-60
    assert abs(float(check['CP_quartet'])-record['CP_quartet'])<1e-12
    for high,low in zip(check['light_masses'],record['all_masses']):
        assert np.max(abs(np.array([float(x) for x in high])/np.array(low[:3])-1))<1e-12


def test_strong_CP_protection_does_not_force_golden_weak_mixing():
    r=R['NB_fixed_mass_kinetic_test'];assert len(r['metrics'])==12
    assert r['four_response_singular_values'][-1]>.5
    assert r['six_decoupling_mass_log_residual']<1e-12
    assert min(q['minimum_bare_metric_eigenvalue'] for q in r['metrics'])>.99
    assert max(q['positive_polynomial_completion_error'] for q in r['metrics'])<1e-60


def test_allowed_dimension_seven_quality_operator():
    r=R['dimension_seven_quality_operator'];q=r['strong_phase_scan']
    assert abs(r['det_L_imaginary'])>1e-6
    assert 900<q[0]['strong_phase']/q[1]['strong_phase']<1100
    assert abs(q[0]['strong_phase'])>1e-5


def test_invalid_dimensions_rank_and_vev_rejected():
    for f,t in [(np.eye(3),np.eye(3)),(np.zeros((3,6)),np.zeros((3,6))),
                (np.hstack([np.eye(3),np.zeros((3,3))]),np.zeros((3,6)))]:
        try:canonical_kernel(f,t)
        except ValueError:pass
        else:raise AssertionError('invalid heavy row accepted')
    for v in [0,-1,np.nan]:
        try:full_spectrum(K[0],v)
        except ValueError:pass
        else:raise AssertionError('invalid Higgs insertion accepted')


if __name__=='__main__':
    suite=unittest.TestSuite(unittest.FunctionTestCase(v) for k,v in sorted(globals().copy().items()) if k.startswith('test_'))
    result=unittest.TextTestRunner(verbosity=2).run(suite);raise SystemExit(not result.wasSuccessful())
