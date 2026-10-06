"""Independent spectral and physical checks of the new invariant receipts."""
import importlib.util
import json
from pathlib import Path
import sys
import numpy as np
import sympy as sp

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))
from develop_valentiner_frames import generators,group_closure,numeric
from perfectpower.flavor_mediator import canonical_mediator


def test_independent_eigenvalue_character_counts():
    receipt=json.loads((ROOT/'receipts/m22_interactions/valentiner_invariants.json').read_text())
    matrices=[numeric(g) for g in group_closure(generators())[0]]
    eigenvalues=np.linalg.eigvals(np.array(matrices))
    # Trace Sym^k from eigenvalue monomials, independently of the rational recurrence.
    chars=[]
    for k in range(7):
        chars.append(sum(eigenvalues[:,0]**a*eigenvalues[:,1]**b*eigenvalues[:,2]**(k-a-b)
                         for a in range(k+1) for b in range(k+1-a)))
    for p in range(7):
        for q in range(7-p):
            average=np.mean(chars[p]*chars[q].conj())
            assert abs(average-receipt['bidegree_dimensions'][f'{p},{q}'])<2e-12
    assert receipt['tensor_dimensions']['6,0']['extra']==1
    assert receipt['tensor_dimensions']['3,3']['extra']==0


def test_polynomial_action_on_complex_triplets():
    receipt=json.loads((ROOT/'receipts/m22_interactions/valentiner_invariants.json').read_text())
    symbols=sp.symbols('x y z')
    expression=sp.sympify(receipt['sextic']['polynomial'],locals=dict(zip(('x','y','z'),symbols)))
    invariant=sp.lambdify(symbols,expression,'numpy')
    rng=np.random.default_rng(220310)
    for _ in range(12):
        v=rng.normal(size=3)+1j*rng.normal(size=3);v/=np.linalg.norm(v)
        for g in generators():
            assert abs(invariant(*(numeric(g)@v))-invariant(*v))<3e-14


def test_canonical_projectors_and_light_heavy_spectrum():
    rng=np.random.default_rng(2260)
    records=[]
    for _ in range(2):
        c=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));m=.7+.2j
        result=canonical_mediator(m*np.eye(3),c,h=.31)
        heavy=result['heavy_row'];light=result['light_right_frame']
        assert np.max(abs(heavy@light))<2e-14
        assert np.max(abs(light.conj().T@light-np.eye(3)))<2e-14
        assert np.linalg.matrix_rank(heavy)==3
        s=np.linalg.svd(c,compute_uv=False)
        assert np.max(abs(np.linalg.svd(heavy,compute_uv=False)-np.sqrt(abs(m)**2+s*s)))<2e-14
        y=result['Y'];eigen,u=np.linalg.eigh(y@y.conj().T)
        _,w=np.linalg.eigh(c@c.conj().T)
        assert np.max(abs(abs(u.conj().T@w)-np.eye(3)))<2e-14
        records.append([np.outer(u[:,i],u[:,i].conj()) for i in range(3)])
    a,b=records
    probability=np.array([[np.trace(x@y).real for y in b] for x in a])
    assert np.max(abs(probability.sum(axis=0)-1))<2e-14
    assert np.max(abs(probability.sum(axis=1)-1))<2e-14
    assert abs(np.trace(a[0]@b[0]@a[1]@b[1]).imag)>1e-5

if __name__=='__main__':
    import unittest
    tests=[unittest.FunctionTestCase(fn) for fn in (
        test_independent_eigenvalue_character_counts,
        test_polynomial_action_on_complex_triplets,
        test_canonical_projectors_and_light_heavy_spectrum)]
    result=unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(tests))
    raise SystemExit(not result.wasSuccessful())
