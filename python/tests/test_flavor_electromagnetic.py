"""Electromagnetic spectral invariance and the exact nominated angle carrier."""
from pathlib import Path
import json,unittest
import numpy as np
from perfectpower.flavor_electromagnetic import *
from perfectpower.flavor_hermitian import block_spectrum
from develop_flavor_electromagnetic import angle_certificate

ROOT=Path(__file__).resolve().parents[2]
SAVED=json.loads((ROOT/'receipts/m22_interactions/flavor_electromagnetic.json').read_text())


def test_exact_angle_certificate_and_conjugates():
    assert angle_certificate()==SAVED['angle_exact_certificate']
    assert SAVED['angle_exact_certificate']['positive_half_circle_small_C_angles']==[6,66,114,174]


def test_mass_fixed_orbit_preserves_photon_screening_but_changes_CP():
    rows=SAVED['phase_orbit'];s=np.array([r['photon_screening_at_spacelike_momenta'] for r in rows])
    assert np.max(abs(s-s[0]))<1e-10
    j=np.array([r['finite_CP_quartet'] for r in rows]);assert np.ptp(j)>5e-5
    assert abs(j[points_index(66)]+j[points_index(-66)])<1e-13


def points_index(angle):
    return [r['initialized_source_frame_phase_degrees'] for r in SAVED['phase_orbit']].index(angle)


def test_recovered_phases_and_real_center_completion():
    for r in SAVED['phase_orbit']:
        expected=r['initialized_source_frame_phase_degrees'];got=r['recovered_unitary_chart']['delta_degrees']
        assert abs((got-expected+180)%360-180)<1e-7
        assert r['electromagnetic_generator_identity_error']<1e-12
        assert r['source_center_reconstruction_error']<1e-50
        assert all(np.isfinite(float(c)) for c in r['real_polynomial_source_coefficients'])


def test_all_state_log_threshold_independent_even_of_source_eigenvalues():
    rng=np.random.default_rng(660137)
    for _ in range(7):
        Z=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));C=(Z+Z.conj().T)/2
        S=block_spectrum(C,1.2,1.,.03)
        assert abs(logarithmic_threshold(S['masses'],2/3)-determinant_log_threshold(1.2,.03,1.,2/3))<1e-12


def test_screening_low_momentum_coefficient_and_scale_covariance():
    Q=1e-3;mass=2.;charge=2/3;colors=3
    # Integral x^2(1-x)^2=1/30 fixes the normalization independently.
    expected=colors*charge**2/(15*np.pi)*(Q/mass)**2
    assert abs(photon_screening(Q,[mass],charge)/expected-1)<1e-7
    assert photon_screening(0,[mass],charge)==0
    assert abs(photon_screening(.4,[mass,.2],charge)-photon_screening(4,[10*mass,2.],charge))<1e-14


def test_gauge_boundary_remains_independent_positive_input():
    screening=SAVED['phase_orbit'][0]['photon_screening_at_spacelike_momenta'][1]
    inv=np.array([130.,137.035999177,145.])-screening
    assert np.all(inv>0) and np.ptp(inv)==15.
    assert SAVED['gauge_boundary_operator']['independent_coefficient']


if __name__=='__main__':
    suite=unittest.TestSuite(unittest.FunctionTestCase(v) for k,v in sorted(globals().copy().items()) if k.startswith('test_'))
    result=unittest.TextTestRunner(verbosity=2).run(suite);raise SystemExit(not result.wasSuccessful())
