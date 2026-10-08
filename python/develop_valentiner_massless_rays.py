"""Exact formal massive elimination on specified null rays, through order twelve.

Ray checks are restrictions, not a multivariate flatness or moduli-space proof.
"""
import json
from pathlib import Path
import sympy as s
from develop_valentiner_frame_selection import full_sextic_polynomial
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions/valentiner_massless_rays.json'


def ray_profile(direction=(1,0,0), order=12):
    data=json.loads((ROOT/'receipts/m22_interactions/valentiner_frame_selection.json').read_text())['nonlinear_massless_branch']
    field=s.QQ.algebraic_field(s.sqrt(5),s.I*s.sqrt(3));zero=field.zero;one=field.one
    cv=lambda z:field.from_sympy(s.sympify(z))
    inv=[[cv(z) for z in row] for row in data['massive_Hessian_inverse']]
    null=[[cv(z) for z in row] for row in data['null_vectors']]
    massive=data['massive_coordinate_indices']
    w=(-1+s.I*s.sqrt(3))/2
    base=[cv(z) for z in (1,0,0,0,w,0,0,0,w*w)]
    vals=[]
    for i in range(9):
        val={}
        if base[i]:val[0]=base[i]
        linear=sum((field.convert(d)*n[i] for d,n in zip(direction,null)),zero)
        if linear:val[1]=linear
        vals.append(val)
    P=full_sextic_polynomial();v=P.gens
    W=P-s.Poly(5*s.Matrix(3,3,v).det(),v,domain=field)
    gradients=[W.diff(v[i]).rep.to_dict() for i in massive]
    def times(A,B,n):
        result={}
        for i,a in A.items():
            for j,b in B.items():
                if i+j<=n:result[i+j]=result.get(i+j,zero)+a*b
        return {k:z for k,z in result.items() if z}
    def evaluate(polys,n):
        cache={(0,)*9:{0:one}}
        def monomial(m):
            if m not in cache:
                i=next(i for i,p in enumerate(m) if p)
                prev=list(m);prev[i]-=1
                cache[m]=times(monomial(tuple(prev)),vals[i],n)
            return cache[m]
        result=[]
        for poly in polys:
            coefficients={}
            for m,c in poly.items():
                for k,z in monomial(m).items():coefficients[k]=coefficients.get(k,zero)+c*z
            result.append({k:z for k,z in coefficients.items() if z})
        return result
    for degree in range(2,order):
        residual=[row.get(degree,zero) for row in evaluate(gradients,degree)]
        for i,index in enumerate(massive):
            correction=-sum((inv[i][j]*residual[j] for j in range(6)),zero)
            if correction:vals[index][degree]=correction
    residual=evaluate(gradients,order-1)
    assert all(not row for row in residual)
    effective=evaluate([W.rep.to_dict()],order)[0]
    return {'null_direction':list(direction),'eliminated_gradient_verified_through':order-1,
            'effective_W_coefficients':{str(n):str(field.to_sympy(effective.get(n,zero))) for n in range(3,order+1)},
            'scope':'One-dimensional restriction; no inference of complete multivariate flatness.'}

if __name__=='__main__':
    rows=[]
    for direction in ((1,0,0),(1,1,0),(1,1,1)):
        rows.append(ray_profile(direction));print(direction,rows[-1]['effective_W_coefficients'],flush=True)
    OUT.write_text(json.dumps({'benchmark':'a=-5,b=1,c=0','rays':rows},indent=2,sort_keys=True)+'\n')
