"""Reconstruct the original tensor slice and audit the exact ideal proof."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import sys
import pytest
import sympy as s

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))
from develop_valentiner_exact_vacuum_curve import block_polynomials, certificate_script, prove


def test_original_tensor_slice_and_exact_hessian():
    W,D=block_polynomials()  # Also verifies all four omitted F-identities.
    assert len(W.terms())==42
    assert s.expand(D.as_expr()-s.Symbol('z')*(s.Symbol('x')*s.Symbol('y')-s.Symbol('p')*s.Symbol('q')))==0
    F=W.domain
    assert s.Poly(s.Symbol('a')**4-4*s.Symbol('a')**2+64).is_irreducible
    omega=(-1+s.I*s.sqrt(3))/2
    base=[F.from_sympy(s.sympify(v)) for v in (1,omega,omega**2,0,0)]
    def ev(poly):
        value=F.zero
        for m,c in poly.rep.to_dict().items():
            term=c
            for v,n in zip(base,m):term*=v**n
            value+=term
        return value
    assert all(ev(W.diff(v))==F.zero for v in W.gens)
    assert ev(D)==F.one
    H=s.polys.matrices.DomainMatrix([[ev(W.diff(v).diff(u)) for u in W.gens[:4]] for v in W.gens[:4]],(4,4),F)
    determinant=H.det()
    a=F.from_sympy(s.sqrt(5)+s.I*s.sqrt(3))
    expected=F.convert(s.Rational(54675,8))*a**3+F.convert(s.Rational(32805,2))*a**2-F.convert(s.Rational(10935,2))*a-F.convert(109350)
    assert determinant==expected and determinant!=F.zero


def test_committed_exact_certificate_integrity():
    folder=ROOT/'receipts/m22_interactions';stem='valentiner_exact_vacuum_curve'
    receipt=json.loads((folder/(stem+'.json')).read_text())
    script=(folder/(stem+'.sing')).read_bytes();log=(folder/(stem+'.log')).read_bytes()
    assert script.decode()==certificate_script()
    assert hashlib.sha256(script).hexdigest()==receipt['script_sha256']
    assert hashlib.sha256(log).hexdigest()==receipt['log_sha256']
    for marker in ('DIM=1','BASIS_SIZE=38','LIFT_IDENTITY=1','COLON_REMAINDERS_ZERO=1','POINT_ON_IDEAL=1','MASSIVE_HESSIAN_INVERTIBLE=1','CONSTANT_W=1','CERTIFICATE_COMPLETE'):
        assert marker in log.decode()
    assert receipt['characteristic']==0 and receipt['local_curve_smooth']
    assert receipt['local_parameter']=='q'


def test_live_characteristic_zero_curve_proof():
    binary=os.environ.get('SINGULAR_BINARY') or shutil.which('Singular')
    if not binary:pytest.skip('Singular optional; exact transcript is committed')
    result=prove(binary)
    assert result['colon_identity_verified'] and result['global_dimension']==1
