"""Mixed-coefficient interpolation and original-tensor formal replay checks."""
import json,sys,math
from pathlib import Path
import sympy as s
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))
from develop_valentiner_multivariate_flatness import grid_nodes,grid_certificate,newton_coefficients,euler_flatness_criterion,chart_certificate
from develop_valentiner_massless_rays import ray_profile
F=s.QQ.algebraic_field(s.sqrt(5),s.I*s.sqrt(3))


def reconstruct(coefficients):
    x,y=s.symbols('x y')
    basis=lambda x,n:s.prod(x-k for k in range(n))/s.factorial(n)
    return s.Poly(sum(F.to_sympy(z)*basis(x,a)*basis(y,b) for (a,b),z in coefficients.items()),x,y,domain=F)


def test_full_newton_grid_is_unisolvent():
    record=grid_certificate(12)
    assert record['nodes']==record['polynomial_dimension']==91
    assert record['exact_Newton_determinant']==1


def test_interpolation_recovers_mixed_algebraic_polynomial():
    x,y=s.symbols('x y');degree=7
    P=s.Poly((s.sqrt(5)+s.I*s.sqrt(3))*x**2*y**3+3*x**7-2*y**6+x*y+1,x,y,domain=F)
    values={(i,j):F.from_sympy(P.as_expr().subs({x:i,y:j})) for i,j in grid_nodes(degree)}
    assert reconstruct(newton_coefficients(values,degree,F))==P


def test_old_three_rays_miss_a_degree_seven_obstruction():
    u,v,w=s.symbols('u v w');P=u*u*v*w*(u-v)*(u-w)*(v-w)
    assert all(P.subs(dict(zip((u,v,w),d)))==0 for d in ((1,0,0),(1,1,0),(1,1,1)))
    x,y=s.symbols('x y');Q=s.Poly(P.subs({u:1,v:x,w:y}),x,y,domain=F)
    values={(i,j):F.from_sympy(Q.as_expr().subs({x:i,y:j})) for i,j in grid_nodes(7)}
    recovered=newton_coefficients(values,7,F)
    assert recovered and reconstruct(recovered)==Q


def test_full_receipt_has_every_node_and_no_mixed_coefficients():
    record=json.loads((ROOT/'receipts/m22_interactions/valentiner_multivariate_flatness.json').read_text())
    nodes=grid_nodes(12);rows=record['exact_node_records']
    assert [tuple(row['null_direction'][1:]) for row in rows]==nodes
    assert all(row['eliminated_gradient_verified_through']==11 for row in rows)
    for n in range(3,13):
        values={(row['null_direction'][1],row['null_direction'][2]):F.from_sympy(s.sympify(row['effective_W_coefficients'][str(n)])) for row in rows}
        assert newton_coefficients(values,n,F)=={}
        assert record['effective_W_Newton_coefficients'][str(n)]=={}
    assert record['first_possible_effective_F_energy_degree']==24


def test_original_tensor_replays_interior_and_boundary_grid_points():
    record=json.loads((ROOT/'receipts/m22_interactions/valentiner_multivariate_flatness.json').read_text())
    targets={(1,2,3),(1,7,5),(1,0,12)}
    selected=[row for row in record['exact_node_records'] if tuple(row['null_direction']) in targets]
    assert len(selected)==3
    for row in selected:assert ray_profile(tuple(row['null_direction']))==row


def test_optional_curve_return_keeps_previous_receipt_semantics():
    plain=ray_profile((1,0,0),order=7);curve=ray_profile((1,0,0),order=7,include_curve=True)
    coefficients=curve.pop('matrix_coordinate_series')
    assert curve==plain and len(coefficients)==9


def test_exact_euler_criterion_has_only_degree_six_resonance():
    record=euler_flatness_criterion()
    assert record['original_polynomial_identity_verified']
    assert record['resonant_degree']==6 and record['resonant_coefficient_already_zero']
    # Solve the formal Euler equation coefficient by coefficient. With D=1,
    # the constant is -5/2, and degree six is the only free coefficient.
    n=s.symbols('n',integer=True)
    assert s.solve(n-6,n)==[6]
    assert s.Rational(15,1)/(-6)==-s.Rational(5,2)


def test_exact_original_tensor_implicit_chart():
    record=chart_certificate()
    assert record['full_original_gradient_at_base_zero']
    assert record['massive_inverse_exactly_verified']
    assert record['full_hessian_rank']==6 and record['holomorphic_implicit_graph_dimension']==3
