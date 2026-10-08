"""Exact three-variable elimination by a provably unisolvent Newton grid.

Coefficient interpolation here is exact over Q(sqrt(5),sqrt(-3)); a complete
triangular grid determines every homogeneous polynomial through the stated
order. This differs from isolated ray evidence.
"""
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
import json
import math
import sympy as s
from develop_valentiner_massless_rays import ray_profile
from develop_valentiner_frame_selection import full_sextic_polynomial
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions/valentiner_multivariate_flatness.json'


def grid_nodes(order):
    return [(i,total-i) for total in range(order+1) for i in range(total+1)]


def newton_coefficients(values,order,field):
    """Exact two-variable finite differences on i+j<=order."""
    answer={}
    for a,b in grid_nodes(order):
        value=sum((field.convert((-1)**(a+b-i-j)*math.comb(a,i)*math.comb(b,j))*values[i,j]
                   for i in range(a+1) for j in range(b+1)),field.zero)
        if value:answer[a,b]=value
    return answer


def grid_certificate(order):
    nodes=grid_nodes(order)
    # B_ab(i,j)=binom(i,a)binom(j,b) is zero at earlier total degrees,
    # and is delta_(a,b),(i,j) within a total-degree block.
    for i,j in nodes:
        for a,b in nodes:
            if a+b>=i+j:
                value=(math.comb(i,a) if i>=a else 0)*(math.comb(j,b) if j>=b else 0)
                assert value==int((i,j)==(a,b))
    return {'order':order,'nodes':len(nodes),'polynomial_dimension':math.comb(order+2,2),
            'Newton_evaluation_matrix':'unit lower triangular in total-degree order',
            'exact_Newton_determinant':1,
            'homogeneous_lift':'Q_n(u)=u0^n*Q_n(1,u1/u0,u2/u0); zero on u0!=0 implies the polynomial is identically zero.'}


def chart_certificate():
    """Check the original tensor, massive inverse and three null coordinates."""
    P=full_sextic_polynomial();v=P.gens;field=P.domain;zero=field.zero
    cv=lambda z:field.from_sympy(s.sympify(z))
    omega=(-1+s.I*s.sqrt(3))/2
    base=[cv(z) for z in (1,0,0,0,omega,0,0,0,omega**2)]
    D=s.Poly(s.Matrix(3,3,v).det(),v,domain=field);W=P-5*D
    def evaluate(poly):
        value=zero
        for m,c in poly.rep.to_dict().items():
            if any(n and not base[i] for i,n in enumerate(m)):continue
            term=c
            for i,n in enumerate(m):
                if n:term*=base[i]**n
            value+=term
        return value
    assert all(evaluate(W.diff(z))==zero for z in v)
    data=json.loads((ROOT/'receipts/m22_interactions/valentiner_frame_selection.json').read_text())['nonlinear_massless_branch']
    indices=data['massive_coordinate_indices'];inv=[[cv(z) for z in row] for row in data['massive_Hessian_inverse']]
    H=[[evaluate(W.diff(a).diff(b)) for b in v] for a in v]
    for i in range(6):
        for j in range(6):
            assert sum((H[indices[i]][indices[k]]*inv[k][j] for k in range(6)),zero)==field.convert(int(i==j))
    null=[[cv(z) for z in row] for row in data['null_vectors']]
    for n in null:
        assert all(sum((row[i]*n[i] for i in range(9)),zero)==zero for row in H)
    free=[3,6,7]
    assert all(null[j][free[i]]==field.convert(int(i==j)) for i in range(3) for j in range(3))
    assert evaluate(D)==field.one and evaluate(W)==field.convert(s.Rational(-5,2))
    return {'full_original_gradient_at_base_zero':True,'massive_coordinate_indices':indices,
            'free_coordinate_indices':free,'massive_inverse_exactly_verified':True,
            'independent_null_vectors_verified':3,'full_hessian_rank':6,
            'holomorphic_implicit_graph_dimension':3}


def euler_flatness_criterion():
    """Exact identity reducing the all-orders question to determinant constancy.

    On the massive implicit graph, E acts on the three free lower entries.
    The original W has only degrees three and six. The known degree-six
    cancellation removes the sole resonant homogeneous solution.
    """
    P=full_sextic_polynomial();v=P.gens;field=P.domain
    D=s.Poly(s.Matrix(3,3,v).det(),v,domain=field)
    W=P-5*D
    euler=sum((s.Poly(z,v,domain=field)*W.diff(z) for z in v),s.Poly(0,v,domain=field))
    assert (euler-6*W-15*D).is_zero
    return {'original_polynomial_identity_verified':True,
            'identity_on_massive_graph':'(E-6) W_eff = 15 D_eff',
            'homogeneous_identity':'(n-6)*W_n=15*D_n',
            'base_determinant':1,'base_effective_W':'-5/2',
            'resonant_degree':6,'resonant_coefficient_already_zero':True,
            'all_orders_equivalence':'All nine F terms vanish locally iff D_eff is identically 1, given W_6=0.',
            'proof_scope':'Exact necessary and sufficient local criterion; determinant constancy to all orders is not asserted.'}


def one_node(task):
    i,j,order=task
    return ray_profile((1,i,j),order=order)


def build(order=12,workers=6):
    nodes=grid_nodes(order);records=[]
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for index,record in enumerate(pool.map(one_node,[(i,j,order) for i,j in nodes]),1):
            records.append(record)
            if index%10==0 or index==len(nodes):print(f'exact grid {index}/{len(nodes)}',flush=True)
    field=s.QQ.algebraic_field(s.sqrt(5),s.I*s.sqrt(3));degrees={}
    for n in range(3,order+1):
        values={(row['null_direction'][1],row['null_direction'][2]):field.from_sympy(s.sympify(row['effective_W_coefficients'][str(n)])) for row in records}
        coeffs=newton_coefficients(values,n,field)
        # Interpolating all nodes must reproduce every supplied value, including
        # the larger order grid beyond the minimal degree-n subset.
        for (i,j),value in values.items():
            predicted=sum((z*field.convert((math.comb(i,a) if i>=a else 0)*(math.comb(j,b) if j>=b else 0)) for (a,b),z in coeffs.items()),field.zero)
            assert predicted==value
        degrees[str(n)]={f'{a},{b}':str(field.to_sympy(z)) for (a,b),z in coeffs.items()}
    first_nonzero=next((n for n in range(3,order+1) if degrees[str(n)]),None)
    return {'benchmark':'a=-5,b=1,c=0; K0=diag(1,omega,omega^2)',
            'exact_field':'Q(sqrt(5),sqrt(-3))','implicit_chart':chart_certificate(),'all_orders_criterion':euler_flatness_criterion(),'unisolvence':grid_certificate(order),
            'effective_W_Newton_coefficients':degrees,
            'all_effective_W_degrees_3_through_order_vanish':all(not row for row in degrees.values()),
            'first_nonzero_effective_W_degree':first_nonzero,
            'first_possible_effective_W_degree':first_nonzero or order+1,
            'first_possible_effective_F_energy_degree':2*(first_nonzero-1) if first_nonzero else 2*order,
            'massive_F_equations_solved_through':order-1,'exact_node_records':records,
            'scope':'Complete multivariate jet through the stated degree, not an all-orders flatness or exact-family proof. Canonical effective metric is regular and positive at the base.'}

if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--order',type=int,default=12);parser.add_argument('--workers',type=int,default=6)
    args=parser.parse_args();record=build(args.order,args.workers)
    OUT.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');print(OUT.relative_to(ROOT))
