"""Symmetry, derivative, spectral and fixed-mass checks for the joint vacuum."""
from pathlib import Path
import sys,json,unittest
import numpy as np
import mpmath as mp
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'python'))
from valentiner_adjoint_uv import *
from valentiner_adjoint_quartics import symmetric_vector,adjoint
from valentiner_rank_lifting import hessian as rank_hessian,DEFAULT_CROSS,cross_operators
from valentiner_source_cp import source_pair_cp_certificate,cp_matrix
from develop_valentiner_adjoint_uv import adjoint_character_certificate,scalar_basis_certificate,independent_CP_invariant,cp_transform
from develop_valentiner_frames import generators,group_closure,numeric
from perfectpower.flavor_kinetic import matrix
from valentiner_adjoint_quarks import match as adjoint_quark_match

P,PROJECTOR_RECORD=quartic_projectors()
RECEIPT=json.loads((ROOT/'receipts/m22_interactions/valentiner_adjoint_uv.json').read_text())
W=np.array(RECEIPT['vacuum']['field_coordinates'])


def test_exact_adjoint_character_counts():
    assert adjoint_character_certificate()=={'End_Sym2_adjoint_singlets':6,'Sym3_adjoint_singlets':1,'full_adjoint_cube_singlets':2}


def test_canonical_quartic_channels_and_seed_independence():
    Q,record=quartic_projectors(seed=23)
    assert [round(np.trace(p)) for p in P]==[1,8,8,9,10]
    assert max(np.linalg.norm(p-q) for p,q in zip(P,Q))<1e-11
    assert np.linalg.norm(sum(P)-np.eye(36))<1e-12
    assert PROJECTOR_RECORD['max_generator_invariance_error']<1e-11
    assert PROJECTOR_RECORD['max_CP_even_invariance_error']<1e-11


def test_exact_source_CP_coset_and_twisted_quartic_count():
    certificate,_=source_pair_cp_certificate()
    assert certificate['exact_CP_fixed_source_pairs']==289
    assert len(certificate['source_pairs_without_a_CP_fixing_transformation'])==1736
    assert certificate['exact_CP_trace_on_quartic_commutant']==4
    assert certificate['CP_even_adjoint_quartics']==5


def test_complete_scalar_trace_independence():
    r=scalar_basis_certificate()
    assert [(v['degree'],v['rank']) for v in r['balanced_source_trace_basis']]==[(2,3),(4,12),(6,41)]
    assert r['complete_renormalizable_scalar_counts_with_adjoint']['total']==30


def test_positive_mediator_quartics_and_analytic_derivative():
    rng=np.random.default_rng(84);z=rng.normal(size=8)+1j*rng.normal(size=8);e=rng.normal(size=8)+1j*rng.normal(size=8)
    value,g=quartic_value_gradient(z,P,QUARTIC_COEFFICIENTS)
    assert value>=QUARTIC_COEFFICIENTS.min()*np.linalg.norm(z)**4-1e-10
    eps=1e-5
    fd=(quartic_value_gradient(z+eps*e,P,QUARTIC_COEFFICIENTS)[0]-quartic_value_gradient(z-eps*e,P,QUARTIC_COEFFICIENTS)[0])/(2*eps)
    assert abs(fd-2*np.real(g@e))<1e-6


def test_full_potential_family_phase_and_CP_covariance():
    rng=np.random.default_rng(70);w=rng.normal(size=70)*.2;x,t=uv_unpack(w);L,A,B=unpack(x);gu,gd,gh=[numeric(g) for g in generators()[:3]]
    q=uv_pack(pack(gu@L@gd.conj().T,gu@A@gh.conj().T,gd@B@gh.conj().T),adjoint(gh)@t)
    z=np.exp(1j*np.pi/3);phase=uv_pack(pack(L,z*A,z**2*B),z*t)
    value=potential(w,P)[0]
    for y in [q,phase,cp_transform(w)]:assert abs(potential(y,P)[0]-value)<1e-8


def test_full_analytic_gradient_by_independent_five_point_displacements():
    rng=np.random.default_rng(917);w=W+.001*rng.normal(size=70);value,g=potential(w,P)
    for _ in range(3):
        e=rng.normal(size=70);h=2e-5
        fd=(-potential(w+2*h*e,P)[0]+8*potential(w+h*e,P)[0]-8*potential(w-h*e,P)[0]+potential(w-2*h*e,P)[0])/(12*h)
        assert abs(fd-g@e)<3e-6*max(1,abs(fd))


def test_rank_lifting_normal_operator_matches_full_hessian_response():
    group=group_closure(generators())[0];gu,gh=numeric(group[12]),numeric(group[36]);v,b=gu[:,0],gh[:,0];a=np.diag([1.,0,0]).astype(complex)
    x=pack(np.eye(3),a,np.outer(v,b.conj()));H=rank_hessian(x,penalties=(300,300));_,_,jac=cross_operators(x,True)
    delta=np.linalg.solve(H,-DEFAULT_CROSS@jac);gamma=v[0]*b[0].conj();force=-gamma.conj()*np.outer(v[1:],b[1:].conj())/3
    omega=np.exp(2j*np.pi/3);phase=np.array([[1,omega**2],[omega,1]])
    expected=(333*force+30*phase*force.conj())/(333**2-30**2)
    assert np.max(abs(unpack(delta)[1][1:,1:]-expected))<1e-12
    assert np.linalg.svd(expected,compute_uv=False)[-1]>1e-6


def test_seventy_real_modes_and_stationary_CP_breaking_vacuum():
    value,g=potential(W,P);assert max(abs(g))<1e-8
    H=hessian(W,P,step=2e-5);assert np.linalg.eigvalsh(H)[0]>7.8
    assert abs(np.linalg.eigvalsh(H)[0]-RECEIPT['vacuum']['stationarity']['minimum_scaled_Hessian_eigenvalue'])<1e-4
    assert RECEIPT['vacuum']['stationarity']['minimum_canonical_scalar_mass_squared']>9e-7
    assert RADIAL_STABILIZER>0


def test_physical_CP_from_an_independent_weak_basis_invariant():
    yu,yd,V,record,down=quarks(W);cert=independent_CP_invariant(yu,yd)
    assert abs(record['J'])>2e-5
    assert abs(float(cert['J_from_weak_basis_invariant'])/record['J']-1)<1e-8
    partner=cp_transform(W);pc=quarks(partner)[3]
    assert abs(pc['J']+record['J'])<1e-12
    assert abs(potential(partner,P)[0]-potential(W,P)[0])<1e-8
    assert max(abs(pc[k]-record[k]) for k in ['Vus','Vcb','Vub'])<1e-12


def test_exact_three_light_right_modes_and_positive_heavy_gaps():
    yu,yd,V,record,down=quarks(W);x,t=uv_unpack(W);L,A,B=unpack(x)
    S=np.sqrt(EPSILON)*RHO**5/MEDIATOR_MASS*np.einsum('a,aij->ij',t,BASIS)
    up=adjoint_quark_match(RHO*L,RHO*A,RHO*B,S,'up')
    heavy_up=up['heavy_row'];heavy_down=down['heavy_row']
    assert heavy_up.shape[1]-np.linalg.matrix_rank(heavy_up)==3
    assert heavy_down.shape[1]-np.linalg.matrix_rank(heavy_down)==3
    assert min(np.linalg.svd(heavy_down,compute_uv=False))>.1
    null=down['light_right_frame']
    assert np.max(abs(heavy_down@null))<1e-11
    assert np.max(abs(null.conj().T@null-np.eye(3)))<1e-11
    assert min(np.ravel(record['spectra']))>1e-8


def test_same_adjoint_enters_both_complete_messenger_chains():
    x,t=uv_unpack(W);L,A,B=unpack(x);S=np.sqrt(EPSILON)*RHO**5/MEDIATOR_MASS*np.einsum('a,aij->ij',t,BASIS)
    up=adjoint_quark_match(RHO*L,RHO*A,RHO*B,S,'up');down=adjoint_quark_match(RHO*L,RHO*A,RHO*B,S,'down')
    assert np.max(abs(up['C'][6:]-S.conj().T))<1e-15
    assert np.max(abs(down['C'][6:]-S))<1e-15
    assert up['M'].shape==down['M'].shape==(9,9)
    assert min(up['heavy_gap'],down['heavy_gap'])>.7


def test_fixed_mass_kinetic_space_still_has_four_observable_directions():
    r=RECEIPT['fixed_mass_kinetic_test']
    assert len(r['metrics'])==12
    assert r['four_response_singular_values'][-1]>.009
    assert r['six_mass_max_log_residual']<1e-9
    assert min(x['minimum_bare_metric_eigenvalue'] for x in r['metrics'])>.98
    assert max(x['positive_completion_error'] for x in r['metrics'])<1e-60


def test_reminimized_UV_deformations_retain_full_rank_and_physical_CP():
    cases=RECEIPT['fully_reminimized_one_percent_UV_deformations']
    assert [x['coefficient_fractional_change'] for x in cases]==[-.01,.01]
    for x in cases:
        assert x['stationarity']['stationarity_max']<1e-8
        assert x['stationarity']['minimum_canonical_scalar_mass_squared']>0
        assert abs(x['observables']['J'])>1e-6
        assert min(np.ravel(x['observables']['spectra']))>1e-8


if __name__=='__main__':
    suite=unittest.TestSuite(unittest.FunctionTestCase(v) for k,v in sorted(globals().copy().items()) if k.startswith('test_'))
    result=unittest.TextTestRunner(verbosity=2).run(suite);raise SystemExit(not result.wasSuccessful())
