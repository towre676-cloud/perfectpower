"""Exact algebra, finite spectra and allowed source deformations."""
from pathlib import Path
import json,unittest
import numpy as np
import mpmath as mp
import sympy as sy
from perfectpower.flavor_hermitian import *
from perfectpower.flavor_quantum import scalar_threshold
from develop_valentiner_hermitian import symbolic_certificate,coupling_certificate
from valentiner_adjoint_quartics import BASIS
ROOT=Path(__file__).resolve().parents[2]
SAVED=json.loads((ROOT/'receipts/m22_interactions/valentiner_hermitian.json').read_text())


def test_symbolic_Vandermonde_CP_certificate():
    assert symbolic_certificate()==SAVED['polynomial_basis_exact_certificate']


def test_generic_basis_determinant_is_cube_of_CP_invariant():
    rng=np.random.default_rng(89101)
    with mp.workdps(80):
        for _ in range(6):
            A=matrix(rng.integers(-3,4,(3,3))+1j*rng.integers(-3,4,(3,3)));B=matrix(rng.integers(-3,4,(3,3))+1j*rng.integers(-3,4,(3,3)))
            R=(A+A.H)/2;T=(B+B.H)/2;M=R*R*T*T*R*T
            expected=8*mp.im(sum(M[i,i] for i in range(3)))**3
            assert abs(mp.det(coordinate_matrix(R,T))-expected)/max(abs(expected),1)<mp.mpf('1e-65')


def test_word_degree_three_has_eight_directions_and_four_has_nine():
    R=sy.diag(1,3,7);T=sy.Matrix([[2,1+sy.I,2-sy.I],[1-sy.I,3,3+2*sy.I],[2+sy.I,3-2*sy.I,4]])
    coord=lambda M:sy.Matrix([M[i,i] for i in range(3)]+[v for i,j in [(0,1),(0,2),(1,2)] for v in [sy.re(M[i,j]),sy.im(M[i,j])]])
    Q=[sy.eye(3),R,R**2,T,R*T+T*R,R**2*T+T*R**2,T**2,R*T**2+T**2*R,R*T**2*R]
    assert sy.Matrix.hstack(*map(coord,Q[:8])).rank()==8
    assert sy.Matrix.hstack(*map(coord,Q)).det()==147197952


def test_word_covariance_Hermiticity_and_generalized_CP():
    rng=np.random.default_rng(89102);A=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));B=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3))
    R=A+A.conj().T;T=B+B.conj().T;U=np.linalg.qr(A)[0]
    for Q,rotated,cp in zip(words(R,T),words(U@R@U.conj().T,U@T@U.conj().T),words(R.conj(),T.conj())):
        assert np.max(abs(Q-Q.conj().T))<1e-11
        assert np.max(abs(rotated-U@Q@U.conj().T))<1e-10
        assert np.max(abs(cp-Q.conj()))<1e-12


def test_positive_word_metric_completion_is_global():
    rng=np.random.default_rng(89103)
    for _ in range(5):
        A=.1*(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)));B=.1*(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)))
        F=sum(c*Q for c,Q in zip(rng.normal(size=9),words(A@A.conj().T,B@B.conj().T)))
        metric=(np.eye(3)+F)@(np.eye(3)+F)+.5*np.eye(3)
        assert np.linalg.eigvalsh(metric)[0]>.499999


def test_complete_nonet_fermion_census():
    c=coupling_certificate();assert c==SAVED['renormalizable_fermion_certificate']
    assert len(c['enumerated_fermion_contractions'])==10
    assert all(sum(t['sector']==s for t in c['enumerated_fermion_contractions'])==5 for s in ['up','down'])


def test_nonet_Hermiticity_and_positive_tree_determinant():
    rng=np.random.default_rng(89105)
    for _ in range(8):
        A=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));H=(A+A.conj().T)/2
        for cs,ca,g in [(1.,.2,.7),(-.4,.9,-2.),(.7,.8,.1)]:
            C=nonet_mix(H,singlet_coupling=cs,adjoint_coupling=ca,eta_coupling=g)
            assert np.max(abs(C-C.conj().T))<1e-14
            assert abs(np.linalg.det(nb_matrix(C,.7,1.3,.2))/(.2*.7*1.3)**3-1)<1e-12


def test_finite_inverse_masses_and_doublet_weights_for_signed_sources():
    y,m,v=1.2,1.,.03;light=v*np.array([1e-5,.003,.9]);h=source_for_light_masses(light,y,m,v)
    for signs in [[1,1,1],[1,-1,1],[-1,-1,-1]]:
        s=block_spectrum(np.diag(h*np.array(signs)),y,m,v)
        assert np.max(abs(s['masses'][:3]/light-1))<1e-12
        assert np.max(abs(abs(np.diag(s['doublet_frame']))-doublet_weights(light,y,m,v)))<1e-12
        assert np.max(abs(s['masses'][3:][::-1]*light/(v*y*m)-1))<1e-12


def test_real_block_spectrum_diagonalizes_generic_complex_source():
    rng=np.random.default_rng(89106);A=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));C=A+A.conj().T;s=block_spectrum(C,.7,1.3,.2)
    assert np.max(abs(s['left'].conj().T@s['mass_matrix']@s['right']-np.diag(s['masses'])))<1e-12
    assert np.max(abs(s['left'].conj().T@s['left']-np.eye(6)))<1e-12


def test_one_loop_pair_reality_for_every_mixed_mode():
    rng=np.random.default_rng(89107);nonet=np.concatenate([np.eye(3)[None,:,:]/np.sqrt(3),BASIS])
    for _ in range(5):
        A=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));C=A+A.conj().T;s=block_spectrum(C,.7,1.3,.2)
        G=np.einsum('ab,bij->aij',rng.normal(size=(91,11)),neutral_vertices(nonet,.7))
        assert paired_vertex_reality(s,G)<1e-14
        assert abs(scalar_threshold(s['mass_matrix'],G,np.diag(np.linspace(.3,3.,91)))['delta_theta'])<1e-11


def test_nonHermitian_vertex_exposes_the_required_structure():
    rng=np.random.default_rng(89108);s=block_spectrum(np.diag([.4,1.,2.]),.7,1.3,.2);G=np.zeros((2,6,6),complex)
    G[0,:3,:3]=np.eye(3);G[1,3:,:3]=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3))
    assert abs(scalar_threshold(s['mass_matrix'],G,np.array([[1.,.3],[.3,2.]]))['delta_theta'])>1e-5


def test_scalar_lock_congruence_positive_and_bound_valid():
    rng=np.random.default_rng(89109);Z=rng.normal(size=(5,5));A=Z.T@Z+np.eye(5);J=rng.normal(size=(3,5))
    H=np.block([[A+J.T@J,-J.T],[-J,np.eye(3)]])
    lower=min(np.linalg.eigvalsh(A)[0],1)/(1+np.linalg.norm(J,2))**2
    assert np.linalg.eigvalsh(H)[0]>=lower
    assert SAVED['scalar_lock']['physical_neutral_scalar_total']==91
    assert SAVED['scalar_lock']['positive_full_Hessian_eigenvalue_lower_bound']>0


def test_same_canonical_action_fits_six_masses_and_four_currents():
    f=SAVED['finite_spectrum_fit'];assert f['maximum_relative_target_residual']<1e-10
    assert all(s['actual_light_mass_relative_residual']<1e-8 for s in f['sectors'])
    assert all(s['source_polynomial_target_error_90_digits']<1e-55 for s in f['sectors'])
    assert abs(f['CP_quartet'])>3e-5 and f['CP_partner_residual']<1e-12
    assert min(f['row_deficit_eigenvalues'])>-1e-12


def test_full_Goldstone_and_gauge_phase_factors_real():
    rng=np.random.default_rng(89110);spectra=[]
    for y in [.7,.6]:
        A=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));spectra.append(block_spectrum(A+A.conj().T,y,1.3,.2))
    up,down=spectra;V=up['left'][:3].conj().T@down['left'][:3]
    for s in spectra:
        Z=s['left'][:3].conj().T@s['left'][:3];G=1j*Z*s['masses'][None,:]/(np.sqrt(2)*.2)
        assert np.max(abs((G*G.T).imag))<1e-14
        assert np.max(abs(np.diag(Z).imag))<1e-14
    left=V*down['masses'][None,:]/.2;right=up['masses'][:,None]*V/.2
    assert np.max(abs((left*right.conj()).imag))<1e-14


def test_fixed_mass_source_deformations_keep_phase_theorem():
    r=SAVED['protected_fixed_mass_response'];assert len(r['branches'])==12
    assert r['fractional_column_normalized_response_singular_values'][-1]>1e-4
    assert max(b['finite_six_mass_relative_residual'] for b in r['branches'])<1e-8
    assert all(b['tree_and_one_loop_phase_theorem_preserved'] for b in r['branches'])


def test_affine_search_exact_real_root_counts_and_sign_completeness():
    a=SAVED['mass_only_affine_candidate_search'];assert a['uses_CKM_targets'] is False;t=sy.symbols('t')
    for sector in a['sectors']:
        assert len(sector['sign_search'])==4;total=0
        for sign in sector['sign_search']:
            P=sy.Poly.from_list([sy.Rational(c) for c in sign['rational_sextic_coefficients']],t)
            assert P.degree()==6 and int(P.count_roots(-sy.oo,sy.oo))==sign['exact_real_root_count']
            branches=[b for b in sector['branches'] if b['signs']==sign['signs']];assert len(branches)==sign['exact_real_root_count'];total+=len(branches)
            for b in branches:
                lo,hi=map(sy.Rational,b['root_interval']);assert P.count_roots(lo,hi)==1
                assert b['source_eigenvalue_relative_residual_80_digits']<1e-20
        assert total==sector['total_branches']
    assert len(a['branch_pairs'])==np.prod([s['total_branches'] for s in a['sectors']])


def test_real_source_coefficients_replay():
    R=np.diag([1.,3.,7.]);T=np.array([[2,1+1j,2-1j],[1-1j,3,3+2j],[2+1j,3-2j,4]]);target=np.array([[3,.2+.1j,.4],[.2-.1j,2,.1j],[.4,-.1j,1]])
    c=polynomial_calibration(R,T,target);assert np.max(abs(evaluate_polynomial(R,T,c['coefficients'])-target))<1e-14
    assert c['target_error']<1e-65


def test_invalid_inputs_rejected():
    for fun in [lambda:source_for_light_masses([0,.2,.3],.6,1.,.03),lambda:nb_matrix(np.array([[1,1j,0],[0,1,0],[0,0,1]]),.6,1.,.03)]:
        try:fun()
        except ValueError:pass
        else:raise AssertionError('Expected ValueError')


if __name__=='__main__':
    suite=unittest.TestSuite(unittest.FunctionTestCase(v) for k,v in sorted(globals().copy().items()) if k.startswith('test_'))
    result=unittest.TextTestRunner(verbosity=2).run(suite);raise SystemExit(not result.wasSuccessful())
