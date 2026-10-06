"""Scalar insertion modules, correlated mediation and all rotated restrictions."""
from pathlib import Path
from fractions import Fraction as F
import json
import numpy as np
import sympy as s
import pytest
from perfectpower.flavor_insertion_running import *
from perfectpower.exact_nonet_algebra import certify_projectors
from perfectpower.nonet_running import quartic_value_gradient
from perfectpower.nonet_potential import sector_features
from perfectpower.quartic_renormalization import polynomial_hessians
from perfectpower.flavor_hermitian import block_spectrum,paired_vertex_reality
from develop_flavor_singlet_mediation import exact_singlet_matching_certificate,scalar_closed_module_certificate
from valentiner_adjoint_quartics import quartic_projectors,BASIS
ROOT=Path(__file__).resolve().parents[2]
SAVED=json.loads((ROOT/'receipts/m22_interactions/flavor_singlet_mediation.json').read_text())

@pytest.fixture(scope='module')
def tensors():
    P=np.array(quartic_projectors()[0]);Q,D,_=certify_projectors(P);return P,Q,D


def test_complete_exact_source_and_Higgs_insertion_maps(tensors):
    P,Q,D=tensors
    for higgs,key,n,count in [(False,'source_insertion_map',14,104),(True,'source_Higgs_insertion_map',15,121)]:
        packet=compile_scalar_insertion_maps(Q,D,include_higgs=higgs);assert packet==SAVED[key]
        assert packet['heavy_mass_insertion_count_per_sector']==n and len(packet['nonzero_tensor_entries'])==count
        assert packet['exact_all_eight_adjoint_components'] and packet['exact_opposite_adjoint_generation_checked']


def component_values_gradient(z,P):
    up=sector_features(z[:10],P);down=sector_features(z[10:20],P);values=np.r_[up[0],down[0],z[20:]@z[20:]/2,up[2][:,0],down[2][:,0]]
    gradient=np.zeros((15,24));gradient[:4,:10]=up[1];gradient[4:8,10:20]=down[1];gradient[8,20:]=z[20:]
    gradient[9:12,:10]=up[3][:,0,:];gradient[12:,10:20]=down[3][:,0,:];return values,gradient

@pytest.mark.parametrize('seed',[17,50,93])
def test_exact_map_against_independent_canonical_Hessian_contraction(tensors,seed):
    P,_,_=tensors;rng=np.random.default_rng(seed);z=rng.normal(size=24);c=rng.normal(size=61)*.02;b=rng.normal(size=15)
    V4=polynomial_hessians(lambda t:quartic_value_gradient(t,P)[1].T@c,z)
    HB=polynomial_hessians(lambda t:component_values_gradient(t,P)[1].T@b,z)
    direct=np.trace(HB@V4);beta=scalar_insertion_beta(b,c,SAVED['source_Higgs_insertion_map'])
    assert direct==pytest.approx(component_values_gradient(z,P)[0]@beta,rel=2e-12,abs=2e-12)


def test_all_singlet_to_adjoint_entries_vanish_for_every_quartic():
    packet=SAVED['source_Higgs_insertion_map'];A=numeric_tensor(packet)
    assert A.shape==(15,15,61);assert np.max(abs(A[9:,:9]))==0 and np.max(abs(A[:9,9:]))==0
    rng=np.random.default_rng(72);b=np.r_[rng.normal(size=9),np.zeros(6)]
    for _ in range(8):
        c=rng.normal(size=61);b+=.001*scalar_insertion_beta(b,c,packet);assert np.all(b[9:]==0)


def test_one_scale_kernel_has_five_constraints_and_four_free_directions():
    cert=protection_kernel_certificate();assert cert==SAVED['one_scale_protection_kernel']
    assert cert['generic_independent_constraint_rank']==5 and len(cert['exact_nullspace_basis'])==4
    N=s.diag(2,2,s.Rational(10,3));ku=s.Matrix([1,2,3]);kd=s.Matrix([2,-1,1])
    for b in cert['exact_nullspace_basis']:
        C=s.Matrix(3,3,list(map(s.sympify,b)));assert C.T*N*ku==s.zeros(3,1) and C*N*kd==s.zeros(3,1)


def test_Bezout_certificates_exclude_every_nonzero_projective_patch():
    proof=SAVED['all_rotated_linear_obstruction'];y,z=s.symbols('y z')
    assert proof['real_signature']==[2,1] and proof['exact_projector_identity']
    for key in ['projective_patch_x_nonzero','projective_patch_x_zero_y_nonzero']:
        patch=proof[key];f=list(map(s.sympify,patch['polynomials']));a=list(map(s.sympify,patch['multipliers']))
        assert s.expand(sum((p*q for p,q in zip(f,a)),s.Integer(0)))==1
        corrupted=a.copy();corrupted[0]+=1
        assert s.expand(sum((p*q for p,q in zip(f,corrupted)),s.Integer(0)))!=1
    assert proof['remaining_z_axis_regeneration']=='6'


def test_rotated_obstruction_regenerates_from_exact_algebra():
    table=json.loads((ROOT/'receipts/m22_interactions/nonet_scalar_loop_algebra.json').read_text())['nonzero_symmetric_products']
    assert rotated_linear_obstruction(table)==SAVED['all_rotated_linear_obstruction']


def test_exact_Gaussian_matching_retains_correlated_fermion_operators():
    answer=exact_singlet_matching_certificate();assert answer==SAVED['exact_singlet_matching']
    sigma,J,Fermion,h,M=s.symbols('sigma J F h M',real=True,nonzero=True)
    assert s.expand(s.sympify(answer['matched_potential_with_source_contact'],locals={'sigma':sigma,'J':J,'F':Fermion,'h':h,'M':M})+h*J*Fermion/M**2+h*h*Fermion**2/(2*M**2))==0


def test_rank_one_mass_matching_and_running_are_exactly_correlated():
    module=scalar_closed_module_certificate(SAVED['source_Higgs_insertion_map'],SAVED['singlet_finite_UV']);assert module==SAVED['closed_singlet_module']
    rank=module['rank_one_mass_coefficient_matrix'];assert rank['exact_matching_minors_checked']==36 and rank['exact_minor_derivatives_checked']==36
    assert rank['independent_rank_one_relations']==8 and rank['scalar_running_preserves_rank_one']
    for row in module['sector_matching_and_beta']:assert row['all_six_adjoint_beta_coefficients_exactly_zero']


def test_singlet_vertices_retain_paired_reality_under_arbitrary_real_mixing():
    rng=np.random.default_rng(175);X=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));C=(X+X.conj().T)/2;q=block_spectrum(C,.7,1.2,.1)
    G=np.zeros((11,6,6),complex)
    for i,B in enumerate(BASIS):G[i,3:,:3]=.3*B
    G[8,3:,:3]=.2*np.eye(3);G[9,3:,3:]=.08*np.eye(3);G[10,:3,:3]=.7*np.eye(3)/np.sqrt(2)
    O,_=np.linalg.qr(rng.normal(size=(11,11)));assert paired_vertex_reality(q,np.einsum('ab,aij->bij',O,G))<1e-15


def test_full_49_scalar_completion_has_CP_and_protected_finite_threshold():
    u=SAVED['singlet_finite_UV'];assert u['full_physical_neutral_scalar_count']==49 and u['all_real_scalars_before_removing_Higgs_Goldstones']==52
    assert u['minimum_full_scalar_Hessian_eigenvalue']>1e-5 and u['source_gradient_norm']<1e-12 and u['Gaussian_source_Schur_residual']<1e-12
    assert abs(u['physical_weak_CP_quartet'])>2.6e-4
    for sector in u['sector_thresholds']:
        assert sector['singlet_heavy_Yukawa']!=0 and sector['matched_heavy_mass']>.89
        assert sector['full_fermion_masses'][2]<.04 and sector['full_fermion_masses'][3]>.9
        assert abs(sector['first_order_neutral_scalar_phase'])<1e-14 and abs(sector['UV_phase_coefficient'])<1e-14
        assert sector['maximum_mixed_vertex_pair_imaginary_part']<1e-14 and sector['relative_correction_norm']<.04
    pole=u['scalar_pole_matching'];assert len(pole['full_UV_masses_squared'])==49 and pole['light_pole_maximum_absolute_error']<1e-11


def test_CP_partner_flips_weak_quartet_at_the_same_full_masses():
    old=json.loads((ROOT/'receipts/m22_interactions/valentiner_nonet_joint.json').read_text());u=SAVED['singlet_finite_UV'];z=np.array(u['source_coordinates']);CP=np.array(old['CP_adjoint_matrix']);frames=[];cpframes=[]
    for f,row in enumerate(u['sector_thresholds']):
        x=z[10*f:10*f+10];eta,tr=x[:2];A=np.einsum('a,aij->ij',x[2:],BASIS);Ac=np.einsum('a,aij->ij',CP@x[2:],BASIS)
        y=[1.2,.57][f];m=row['matched_heavy_mass'];q=block_spectrum((.1*eta+.7*tr)*np.eye(3)+.8*A,y,m,z[20]/np.sqrt(2));qc=block_spectrum((.1*eta+.7*tr)*np.eye(3)+.8*Ac,y,m,z[20]/np.sqrt(2))
        assert qc['masses']==pytest.approx(q['masses'],abs=1e-14);frames.append(q['doublet_frame']);cpframes.append(qc['doublet_frame'])
    V=frames[0].conj().T@frames[1];Vc=cpframes[0].conj().T@cpframes[1]
    quartet=lambda V:np.imag(V[0,0]*V[1,1]*V[0,1].conjugate()*V[1,0].conjugate())
    assert abs(Vc)**2==pytest.approx(abs(V)**2,abs=1e-13);assert quartet(Vc)==pytest.approx(-quartet(V),abs=1e-13)


def test_insertion_input_domain_rejection():
    with pytest.raises(ValueError):scalar_insertion_beta(np.zeros(14),np.zeros(61),SAVED['source_Higgs_insertion_map'])
