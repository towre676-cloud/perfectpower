"""Original-tensor checks, symmetry tests and exact selection witnesses."""
from pathlib import Path
import sys,json
import numpy as np
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))
from develop_valentiner_frame_selection import full_sextic_polynomial, invariant_selection, orbit_census, nonlinear_profile, stabilizer_lie_certificate
from develop_valentiner_link import coefficient_functions
from develop_valentiner_frames import generators,group_closure,numeric


def numeric_action():
    P=full_sextic_polynomial();v=P.gens;d=s.Matrix(3,3,v).det()
    W=d+P.as_expr()+d*d
    gradient=s.lambdify(v,[s.diff(W,q) for q in v],'numpy',cse=True)
    target=3*(1/34)**(2/3)
    def V(K):
        A=K.conj().T@K;N=np.trace(A).real
        G=np.linalg.norm(A-N*np.eye(3)/3)**2
        return np.linalg.norm(gradient(*K.flatten()))**2+(N-target)**2+G
    return V,gradient


def test_full_polynomial_matches_original_tensor():
    P=full_sextic_polynomial();value=s.lambdify(P.gens,P.as_expr(),'numpy',cse=True)
    _,I6,_=coefficient_functions();rng=np.random.default_rng(108025)
    for _ in range(6):
        K=.3*(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)))
        assert abs(value(*K.flatten())-I6(K.conj()).conjugate())<2e-13


def test_global_selector_original_F_terms_and_competitors():
    V,gradient=numeric_action();r=np.cbrt(-1/34)
    matrices=group_closure(generators())[0]
    for index in (0,1,4,103,501,1079):
        K=r*numeric(matrices[index]).conj()
        assert V(K)<1e-25
    omega=np.exp(2j*np.pi/3);D=np.diag([1,omega,omega**2])*complex(-1/7)**(1/3)
    assert np.linalg.norm(gradient(*D.flatten()))<2e-13 and V(D)>.2
    q=(-5+1j*np.sqrt(15))/4;p=np.sqrt(q)
    K=np.diag([1,1,p])*complex(-p/((15+13*q)/2+2*q))**(1/3)
    assert np.linalg.norm(gradient(*K.flatten()))<2e-13 and V(K)>.2
    assert V(np.zeros((3,3)))>0


def test_CP_and_product_group_invariance():
    V,_=numeric_action();rng=np.random.default_rng(108028)
    K=.2*(rng.normal(size=(3,3))+1j*rng.normal(size=(3,3)))
    g,h=[numeric(x).conj() for x in generators()[2:]]
    assert abs(V(g@K@h.conj().T)-V(K))<2e-12
    data=json.loads((ROOT/'receipts/m22_interactions/valentiner_cp.json').read_text())
    CP=np.array([[complex(s.sympify(z).evalf()) for z in row] for row in data['unitary_CP_matrix']])
    assert abs(V(CP.conj()@K.conj()@CP.T)-V(K))<2e-12


def test_exact_Euler_phase_bound():
    t,z=s.symbols('t z',real=True)
    # Unit-circle phase e: product with its inverse avoids trigonometric rounding.
    e=s.symbols('e',nonzero=True)
    expression=s.expand(((16+t)*e-t*e**2)*((16+t)/e-t/e**2))
    assert s.expand(expression-256-2*t*(16+t)*(1-(e+1/e)/2))==0
    certificate=invariant_selection()
    assert certificate['soft_example_first_order_energies']['equal_squares']<0
    assert all(certificate['soft_example_first_order_energies'][k]>0 for k in ('distinct_squares','two_equal_squares'))


def test_exact_orbit_stabilizers_and_diagonal_intersections():
    record=orbit_census()
    assert record['certified_nonzero_vacua']==130680
    assert record['certified_off_diagonal_vacua']+108==130680
    assert record['stabilizer_orders']=={'group':1080,'nonunitary':24,'massless':36}


def test_nonlinear_massive_relaxation_through_sixth_order():
    record=nonlinear_profile()
    assert record['raw_null_superpotential_quartic']!='0'
    assert record['effective_superpotential_degrees_3_4_5']==['0','0','0']
    assert record['effective_superpotential_degree_6']=='0'
    assert record['first_possible_effective_F_energy_degree']==12


def test_exact_tensor_stabilizer_has_no_continuous_directions():
    record=stabilizer_lie_certificate()
    assert record['exact_Gram_comparisons']==64 and record['rank']==8
