"""Transport the all-orders block curve into all three null directions."""
from pathlib import Path
import json
import sympy as s
from sympy.polys.matrices import DomainMatrix
from develop_valentiner_frame_selection import full_sextic_polynomial

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions/valentiner_three_exact_curves.json'


def prove():
    P=full_sextic_polynomial();F=P.domain
    omega=F.from_sympy((-1+s.I*s.sqrt(3))/2)
    permutation=[3*((i//3+1)%3)+(i%3+1)%3 for i in range(9)]
    assert all(permutation[permutation[permutation[i]]]==i for i in range(9))
    assert (omega**2)**3==F.one
    W=P-5*s.Poly(s.Matrix(3,3,P.gens).det(),P.gens,domain=F)
    transformed={}
    for m,c in W.rep.to_dict().items():
        n=[0]*9
        for i,v in enumerate(m):n[permutation[i]]=v
        transformed[tuple(n)]=c*(omega**2)**sum(m)
    assert transformed==W.rep.to_dict()
    def action(v):return [omega**2*v[j] for j in permutation]
    base=[F.one,F.zero,F.zero,F.zero,omega,F.zero,F.zero,F.zero,omega**2]
    assert action(base)==base and action(action(action(base)))==base
    data=json.loads((ROOT/'receipts/m22_interactions/valentiner_frame_selection.json').read_text())['nonlinear_massless_branch']
    null=[[F.from_sympy(s.sympify(c)) for c in v] for v in data['null_vectors']]
    tangent=[null[0],action(null[0]),action(action(null[0]))]
    assert action(tangent[-1])==tangent[0]
    matched=[]
    for v in tangent:
        k=next(i for i in (3,6,7) if v[i])
        n=null[(3,6,7).index(k)]
        assert all(v[i]==v[k]*n[i] for i in range(9))
        matched.append(k)
    assert set(matched)=={3,6,7}
    assert DomainMatrix(tangent,(3,9),F).rank()==3
    original=json.loads((ROOT/'receipts/m22_interactions/valentiner_exact_vacuum_curve.json').read_text())
    assert original['local_curve_smooth'] and original['all_nine_original_F_terms_zero_to_all_orders']
    result={
        'transformation':'T(K)=omega^2 A K A^-1, A cycles the three coordinates',
        'W_invariance_verified_on_original_tensor':True,'base_fixed':True,'transformation_order':3,
        'exact_curve_count':3,'tangent_rank':3,'null_coordinate_indices':matched,
        'tangent_vectors':[[str(F.to_sympy(c)) for c in v] for v in tangent],
        'all_nine_F_terms_vanish_on_each_curve':True,'determinant_on_each_curve':1,
        'W_on_each_curve':'-5/2',
        'local_intersections':'Distinct tangents imply pairwise isolated intersections at the base.',
        'scope':'Three individually exact curves span the Hessian kernel. Their union has dimension one; a shared three-dimensional flat germ is not established.',
    }
    OUT.write_text(json.dumps(result,indent=2)+'\n');return result


if __name__=='__main__':print(json.dumps(prove(),indent=2))
