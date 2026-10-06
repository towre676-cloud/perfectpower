"""Scalar one-loop multiplication from polynomial Hessians.

For canonical real scalars, 16 pi^2 beta(V4)=Tr[(Hess V4)^2]/2.
The polarization is a commutative, generally nonassociative algebra.
Numerical basis reconstruction has independent off-grid validation; it is
not a formal rational tensor certificate. Gauge/Yukawa terms are excluded.
"""
import numpy as np


def polynomial_hessians(gradient,x,step=.125):
    """Exact-in-degree Richardson derivative of cubic polynomial gradients."""
    x=np.asarray(x,float);n=len(x);g=np.asarray(gradient(x));out=np.empty(g.shape+(n,))
    for j in range(n):
        e=np.zeros(n);e[j]=step
        coarse=(gradient(x+e)-gradient(x-e))/(2*step)
        fine=(gradient(x+e/2)-gradient(x-e/2))/step
        out[...,j]=(4*fine-coarse)/3
    return (out+np.swapaxes(out,-1,-2))/2


def compile_loop_algebra(value_gradient,field_count,operator_count,seed=1847,samples=128):
    if samples<operator_count:raise ValueError('At least as many samples as operators required')
    rng=np.random.default_rng(seed);points=rng.normal(size=(samples,field_count))
    values=[];hs=[]
    for x in points:
        v,g=value_gradient(x);values.append(v)
        hs.append(polynomial_hessians(lambda y:value_gradient(y)[1],x))
    values=np.asarray(values);hs=np.asarray(hs)
    if values.shape!=(samples,operator_count) or hs.shape!=(samples,operator_count,field_count,field_count):
        raise ValueError('Value/gradient dimensions do not match the declared quartic basis')
    singular=np.linalg.svd(values,compute_uv=False)
    if singular[-1]<1e-9:raise ValueError('Dependent or numerically ill-conditioned operator basis')
    products=.5*np.einsum('pmij,pnij->pmn',hs,hs,optimize=True)
    coefficients=(np.linalg.pinv(values,rcond=1e-12)@products.reshape(samples,-1)).reshape(operator_count,operator_count,operator_count)
    coefficients=(coefficients+np.swapaxes(coefficients,1,2))/2
    fit=values@coefficients.reshape(operator_count,-1)-products.reshape(samples,-1)
    error=float(np.max(abs(fit))/max(1,np.max(abs(products))))
    tests=[]
    for _ in range(6):
        x=rng.normal(size=field_count);v,g=value_gradient(x)
        H=polynomial_hessians(lambda y:value_gradient(y)[1],x)
        direct=.5*np.einsum('mij,nij->mn',H,H,optimize=True)
        recovered=np.einsum('k,kmn->mn',v,coefficients)
        tests.append(float(np.max(abs(direct-recovered))/max(1,np.max(abs(direct)))))
    if max(tests)>1e-8:raise ValueError('Quartic basis is not closed under the scalar loop contraction')
    coefficients[abs(coefficients)<1e-9]=0
    return coefficients,{'field_count':field_count,'operator_count':operator_count,
      'sample_count':samples,'minimum_basis_singular_value':float(singular[-1]),
      'basis_condition_number':float(singular[0]/singular[-1]),'fit_relative_error':error,
      'off_grid_relative_errors':tests,'normalization':'16*pi^2 beta(V4)=Tr[(Hess V4)^2]/2',
      'scope':'Canonical-real-scalar quartic contribution only. Numerical operator reconstruction, no gauge, Yukawa, Higgs or matching-threshold terms.'}


def loop_product(algebra,left,right):
    return np.einsum('kmn,m,n->k',algebra,left,right,optimize=True)


def generated_subalgebra(algebra,seed_vectors,tolerance=1e-8):
    n=algebra.shape[0];B=np.asarray(seed_vectors,float).reshape(-1,n).T;history=[]
    for _ in range(n):
        U,s,_=np.linalg.svd(B,full_matrices=False);rank=int(sum(s>tolerance*max(s[0],1)))
        B=U[:,:rank];history.append(rank)
        products=np.einsum('kmn,ma,nb->kab',algebra,B,B,optimize=True).reshape(n,-1)
        joined=np.column_stack([B,products]);uu,ss,_=np.linalg.svd(joined,full_matrices=False)
        new=int(sum(ss>tolerance*max(ss[0],1)))
        if new==rank:
            leakage=float(np.max(abs(products-B@(B.T@products))))
            return B,{'dimension':rank,'dimension_history':history,'closure_projection_error':leakage}
        B=uu[:,:new]
    raise RuntimeError('Subalgebra iteration did not stabilize')


def exact_two_scalar_rank_certificate():
    import sympy as s
    x,y,a,b,c,k,u,v=s.symbols('x y a b c k u v');V=a*x**4+b*x*x*y*y+c*y**4
    H=s.hessian(V,(x,y));beta=s.expand(s.trace(H*H)/2)
    ba=s.expand(beta).coeff(x,4);bc=s.expand(beta).coeff(y,4)
    bb=s.expand(beta).coeff(x,2).coeff(y,2)
    drift=s.factor((2*b*bb-4*(c*ba+a*bc)).subs({a:k*u*u,b:2*k*u*v,c:k*v*v}))
    assert drift==-128*k**3*u*u*v*v*(u-v)**2
    return {'beta_a':str(ba),'beta_b':str(bb),'beta_c':str(bc),
      'rank_one_relation':'b^2-4*a*c=0','rank_one_relation_beta_on_surface':str(drift),
      'preserved_nontrivial_radial_case':'u=v',
      'scope':'Exact pure-light-scalar one-loop EFT result, 16*pi^2 beta normalization. Failure of a tree matching identity under running does not rule out calculable UV matching.'}


def exact_soft_mediator_counterterm_certificate():
    """Exact scalar UV/EFT distinction for a softly coupled Gaussian mediator."""
    import sympy as s
    x,y,S,a,b,g,u,v,M=s.symbols('x y S a b g u v M')
    V=a*x**4+b*y**4+M**2*S*S/2+g*S*(u*x*x+v*y*y)
    H=s.hessian(V,(x,y,S));counter=s.expand(s.trace(H*H)/2)
    quartic=s.Add(*[term for term in counter.as_ordered_terms() if s.Poly(term,x,y,S).total_degree()==4])
    assert s.expand(quartic-72*a*a*x**4-72*b*b*y**4)==0
    return {'UV_scalar_counterterm_16pi2':str(counter),'UV_quartic_counterterm_16pi2':str(quartic),
      'no_hard_mediator_quartic_counterterm':True,'no_source_cross_quartic_in_this_separated_UV_fixture':True,
      'EFT_tree_exchange':'-g^2 (u*x^2+v*y^2)^2/(2*M^2)',
      'power_counting':'Every external mediator needs a dimension-one current coupling. A local divergent counterterm of dimension d has coefficient dimension 4-d, with no inverse masses. For mediator cubics, mediator quartics and mediator2*source2 quartics the required coupling degree exceeds 4-d.',
      'scope':'Renormalizable perturbative soft-current theory in a mass-independent scheme, without hard mediator gauge/Yukawa/scalar couplings. Finite thresholds and higher-dimensional effective interactions are not zero.'}
