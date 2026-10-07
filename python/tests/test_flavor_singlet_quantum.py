from pathlib import Path
import json
import numpy as np
import pytest
import sympy as s
from scipy.optimize import brentq
from perfectpower.flavor_singlet_quantum import (exact_fermion_counterterms,
    exact_portal_regeneration,non_gaussian_matching_certificate,fermion_effective_potential,
    fixed_spectrum_orbit_certificate,non_gaussian_vacuum_extension)
from perfectpower.flavor_hermitian import block_spectrum

ROOT=Path(__file__).resolve().parents[2]

def receipt():
    return json.loads((ROOT/'receipts/m22_interactions/flavor_singlet_quantum.json').read_text())

def test_exact_trace_and_complete_polynomial_replay():
    packet=exact_fermion_counterterms()
    assert packet==receipt()['fermion_counterterms']
    assert all(v['field_degree']<=4 for v in packet['monomials'])
    assert {v['field_degree'] for v in packet['monomials']}=={0,1,2,3,4}

def test_independent_random_block_traces():
    rng=np.random.default_rng(179)
    for _ in range(12):
        X=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));C=(X+X.conj().T)/2
        a,m=rng.uniform(.1,2,2);D=np.block([[a*np.eye(3),np.zeros((3,3))],[C,m*np.eye(3)]])
        expected=np.trace(C@C@C@C)+2*(a*a+m*m)*np.trace(C@C)+3*(a**4+m**4)
        assert np.trace((D.conj().T@D)@(D.conj().T@D))==pytest.approx(expected,abs=1e-10)

def test_rg_scale_normalization():
    spectrum=block_spectrum(np.diag([.3,.7,1.2]),.8,.9,.2)
    step=1e-5
    derivative=(fermion_effective_potential([spectrum],np.exp(step))-fermion_effective_potential([spectrum],np.exp(-step)))/(2*step)
    box=-6*np.sum(spectrum['masses']**4)
    assert 16*np.pi**2*derivative+box==pytest.approx(0,abs=1e-8)

def test_sigma_self_and_source_regeneration():
    p=receipt()['fermion_counterterms'];symbols={k:s.Symbol(k,real=True) for k in ['e','b','g','y','h','m0','eta','trace','N','T','H','sigma']}
    f=s.sympify(p['polynomial'],locals=symbols);sigma=symbols['sigma'];h=symbols['h'];m=symbols['m0']
    assert s.expand(f.coeff(sigma,4)+18*h**4)==0
    assert s.expand(f.coeff(sigma,3)+72*m*h**3)==0
    assert f.coeff(sigma,2).coeff(symbols['H'])==0
    assert f.coeff(sigma,2).coeff(symbols['N'])==-12*symbols['g']**2*h**2

def test_scalar_portal_hessian_contraction():
    sigma=s.Symbol('sigma',real=True);a=s.symbols('a0:8',real=True);h=s.symbols('h0:4',real=True)
    k,r=s.symbols('k r',real=True);N=sum(x*x for x in a);H=sum(x*x for x in h)/2
    variables=(sigma,*a,*h)
    trace=s.trace(s.hessian(k*sigma*sigma*N,variables)*s.hessian(r*H*N,variables))
    assert s.expand(trace-32*k*r*sigma*sigma*H)==0
    assert exact_portal_regeneration()==receipt()['scalar_portal_regeneration']

def test_non_Gaussian_series_replay():
    assert non_gaussian_matching_certificate()==receipt()['non_Gaussian_matching']

def test_non_Gaussian_vacuum_jet_and_bounded_forms():
    assert non_gaussian_vacuum_extension()==receipt()['non_Gaussian_local_extension']

def test_non_Gaussian_branch_response_and_canonical_metric():
    x=np.array([.12,.08]);q=x*x;g=np.array([.1,.13]);k=np.array([.03,-.02]);M=2.;r3=.07;r4=.09
    def sigma(q):
        return brentq(lambda x:(M*M+k@q)*x+r3*x*x+r4*x**3+g@q,-1,1,xtol=1e-15)
    v=sigma(q);curvature=M*M+k@q+2*r3*v+3*r4*v*v
    gradient=-2*x*(g+k*v)/curvature
    numeric=np.array([(sigma((x+np.eye(2)[i]*1e-5)**2)-sigma((x-np.eye(2)[i]*1e-5)**2))/(2e-5) for i in range(2)])
    assert np.max(abs(gradient-numeric))<1e-10
    metric=np.eye(2)+np.outer(gradient,gradient)
    assert min(np.linalg.eigvalsh(metric))>=1-1e-14
    B=np.outer([.06,-.04],gradient)
    assert np.linalg.det(B)==pytest.approx(0,abs=1e-18)
    assert -.04*(.06*v)-.06*(-.04*v)==pytest.approx(0,abs=1e-18)

def test_full_singlet_orbits_preserve_masses_and_loop_energy():
    old=json.loads((ROOT/'receipts/m22_interactions/flavor_singlet_mediation.json').read_text())
    x=fixed_spectrum_orbit_certificate(old['singlet_finite_UV']);assert x==receipt()['fixed_spectrum_orbits']
    assert len(x['orbits'])==8
    assert max(v['maximum_Dirac_mass_change'] for v in x['orbits'])<3e-15
    assert max(abs(v['source_current_change']) for v in x['orbits'])<1e-15
    assert max(abs(v['fermion_CW_change']) for v in x['orbits'])<1e-15
    assert np.ptp([v['physical_quartet'] for v in x['orbits']])>1e-5

def test_domain_rejections():
    for n in [0,-1,1.5]:
        with pytest.raises(ValueError):exact_fermion_counterterms(n)
        with pytest.raises(ValueError):exact_portal_regeneration(n)
    with pytest.raises(ValueError):fermion_effective_potential([],scale=0)
    with pytest.raises(ValueError):fermion_effective_potential([{'masses':[-1]*6}])
