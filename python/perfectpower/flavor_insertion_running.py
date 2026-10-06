"""Exact scalar running of quadratic-source heavy-mass insertions.

This is the scalar Hessian contribution, not a complete fermion/gauge EFT
anomalous dimension. The field and kinetic conventions are the source nonet.
"""
from fractions import Fraction as F
from functools import lru_cache
import numpy as np
from . import exact_nonet_algebra as E

SINGLET_NAMES=['eta2','s2','eta_s','adjoint_norm']
ADJOINT_NAMES=['eta_A','s_A','A2_8']
INSERTION_NAMES=([f'{q}_{f}' for f in ['up','down'] for q in SINGLET_NAMES]+[f'{q}_{f}' for f in ['up','down'] for q in ADJOINT_NAMES])
CURRENT_NORMS=[F(2),F(2),F(10,3)]


def _contract(H,K):
    """Tr(G^-1 H_insertion G^-1 H_V), coefficientwise in Q(sqrt5)."""
    metric=[1,1,*E.METRIC,1,1,*E.METRIC,1,1,1,1];out={}
    for i,j in H.keys()&K.keys():
        for m,a in H[i,j].items():
            for n,b in K[i,j].items():
                k=tuple(sorted(m+n));c=E.scale(E.mul(a,b),F(1,metric[i]*metric[j]));out[k]=E.add(out.get(k,E.ZERO),c)
    return {m:c for m,c in out.items() if c!=E.ZERO}


def _expand(p,basis):
    coefficients=[]
    for b in basis:
        monomial=next(iter(b));v=b[monomial];assert v[1]==0 and v[0]!=0
        coefficients.append(E.scale(p.get(monomial,E.ZERO),1/v[0]))
    reconstructed=E.padd(*(E.pscale(b,c) for b,c in zip(basis,coefficients)))
    assert reconstructed==p,('Operator tensor outside declared quadratic space',p,reconstructed)
    return coefficients


def compile_scalar_insertion_maps(Q,D,include_higgs=False):
    """14-by-14-by-52 operator action; verify all eight adjoint components."""
    q1,c1,_=E.sector_polys(0,Q,D);q2,c2,_=E.sector_polys(10,Q,D);quartics=E.extended_quartics(Q,D) if include_higgs else E.exact_quartics(Q,D);HV=[E.hessian_polys(p) for p in quartics]
    singlets=q1+q2
    if include_higgs:singlets.append(E.pscale(E.padd(*(E.power(E.var(i),2) for i in range(20,24))),(F(1,2),F(0))))
    adjoff=len(singlets);names=INSERTION_NAMES[:8]+(['Higgs_norm'] if include_higgs else [])+INSERTION_NAMES[8:];entries=[];comparisons=0
    for j,p in enumerate(singlets):
        H=E.hessian_polys(p)
        for k,K in enumerate(HV):
            lhs=_contract(H,K);coeff=_expand(lhs,singlets);comparisons+=len(lhs)
            for i,c in enumerate(coeff):
                if c!=E.ZERO:entries.append([i,j,k,str(c[0]),str(c[1])])
    first=None
    for component in range(8):
        basis=[c[component] for c in c1+c2];block=[]
        for j,p in enumerate(basis):
            H=E.hessian_polys(p)
            for k,K in enumerate(HV):
                lhs=_contract(H,K);coeff=_expand(lhs,basis);comparisons+=len(lhs)
                for i,c in enumerate(coeff):
                    if c!=E.ZERO:block.append([adjoff+i,adjoff+j,k,str(c[0]),str(c[1])])
        if first is None:first=block
        else:assert block==first,('Adjoint components disagree',component)
    entries+=first
    # Exact check of all 18 opposite-sector adjoint transitions across 52 quartics.
    lookup={(i,j,k):(F(a),F(b)) for i,j,k,a,b in entries}
    for i in range(3):
        for j in range(3):
            for k in range(len(quartics)):
                assert lookup.get((adjoff+3+j,adjoff+i,k),E.ZERO)==((CURRENT_NORMS[i],F(0)) if k==40+3*i+j else E.ZERO)
                assert lookup.get((adjoff+i,adjoff+3+j,k),E.ZERO)==((CURRENT_NORMS[j],F(0)) if k==40+3*i+j else E.ZERO)
    return {'operator_names':names,'quartic_count':len(quartics),'heavy_mass_insertion_count_per_sector':len(names),'singlet_module_dimension':adjoff,
            'nonzero_tensor_entries':entries,'quadratic_monomial_comparisons':comparisons,
            'exact_all_eight_adjoint_components':True,'exact_opposite_adjoint_generation_checked':True,
            'normalization':'16*pi^2 beta(B)=Tr[(G^-1 Hess B)(G^-1 Hess V4)]',
            'scope':'Complete quadratic-source heavy-mass scalar-loop map on the declared original fields, including all four Higgs coordinates when requested. Mediator, derivative and fermion/gauge insertion diagrams are excluded.'}


def numeric_tensor(packet):
    n=packet['heavy_mass_insertion_count_per_sector'];out=np.zeros((n,n,packet['quartic_count']))
    for i,j,k,a,b in packet['nonzero_tensor_entries']:out[i,j,k]=float(F(a))+np.sqrt(5)*float(F(b))
    return out


def scalar_insertion_beta(coefficients,quartics,packet):
    b=np.asarray(coefficients,float);c=np.asarray(quartics,float)
    if b.shape[-1:]!=(packet['heavy_mass_insertion_count_per_sector'],) or c.shape!=(packet['quartic_count'],):raise ValueError('Matching insertion and quartic coefficient counts required')
    return np.einsum('ijk,...j,k->...i',numeric_tensor(packet),b,c)


def protection_kernel_certificate():
    import sympy as s
    x=s.symbols('c0:9');C=s.Matrix(3,3,x);ku=s.Matrix([1,2,3]);kd=s.Matrix([2,-1,1]);N=s.diag(2,2,s.Rational(10,3))
    equations=list(C.T*N*ku)+list(C*N*kd);J=s.Matrix(equations).jacobian(x);assert J.rank()==5 and len(J.nullspace())==4
    for v in J.nullspace():assert J*v==s.zeros(6,1)
    return {'current_norm_metric':['2','2','10/3'],'up_to_down_generation':'C.T N k_up','down_to_up_generation':'C N k_down',
            'constraints_for_nonzero_vectors':'C.T N k_up=0 and C N k_down=0','generic_independent_constraint_rank':5,
            'remaining_cross_current_dimensions':4,'exact_witness_vectors':{'up':['1','2','3'],'down':['2','-1','1']},
            'exact_nullspace_basis':[list(map(str,v)) for v in J.nullspace()],
            'general_parameterization':'C=E_up T E_down.T, with the two columns of E_f spanning the orthogonal complement of N k_f, and arbitrary real 2-by-2 T.',
            'scope':'One-scale scalar-generation constraints for both heavy sectors; these conditions are not automatically stable under the joint quartic and insertion flow.'}


def adjoint_rg_polynomials(table):
    import sympy as s
    labels=['radial_up','finite_self_up','radial_down','finite_self_down','singlet_cross','ordinary_cross','finite8_cross','finite9_cross','pair5_cross']
    indices=[10,11,22,23,39,48,49,50,51];x=s.symbols('r_u a_u r_d a_d b h x y z');position={i:j for j,i in enumerate(indices)};beta=[s.Integer(0)]*9
    for k,i,j,c in table:
        if i in position and j in position:
            assert k in position
            beta[position[k]]+=s.Rational(c)*x[position[i]]*x[position[j]]*(1 if i==j else 2)
    return x,[s.factor(v) for v in beta],labels,indices


def _bezout_one(polynomials,variables,max_degree=8):
    """Find exact small rational multipliers for an empty projective patch."""
    import sympy as s
    from itertools import product
    polynomials=[s.Poly(p,*variables).clear_denoms()[1].primitive()[1] for p in polynomials];n=len(variables)
    def monomials(degree):return [v for v in product(range(degree+1),repeat=n) if sum(v)<=degree]
    for degree in range(max(p.total_degree() for p in polynomials),max_degree+1):
        rows=monomials(degree);row_index={m:i for i,m in enumerate(rows)};columns=[];owners=[]
        for k,p in enumerate(polynomials):
            for m in monomials(degree-p.total_degree()):
                col={tuple(i+j for i,j in zip(m,e)):c for e,c in p.terms()};columns.append(col);owners.append((k,m))
        M=s.zeros(len(rows),len(columns));rhs=s.zeros(len(rows),1);rhs[row_index[(0,)*n]]=1
        for j,col in enumerate(columns):
            for m,c in col.items():M[row_index[m],j]=c
        try:solution,parameters=M.gauss_jordan_solve(rhs)
        except ValueError:continue
        solution=solution.subs({p:0 for p in parameters});multipliers=[s.Integer(0)]*len(polynomials)
        for a,(k,m) in zip(solution,owners):multipliers[k]+=a*s.prod(v**e for v,e in zip(variables,m))
        identity=s.expand(sum((a*p.as_expr() for a,p in zip(multipliers,polynomials)),s.Integer(0)));assert identity==1
        return {'polynomials':[str(p.as_expr()) for p in polynomials],'multipliers':[str(s.expand(p)) for p in multipliers],'identity':'1','certificate_total_degree':degree}
    raise AssertionError('No small exact Bezout certificate found')


def rotated_linear_obstruction(table):
    """All real rotated linear subalgebras with independent radial quartics."""
    import sympy as s
    variables,beta,labels,indices=adjoint_rg_polynomials(table);ru,au,rd,ad,b,h,x,y,z=variables
    only={v:0 for v in [ru,au,rd,ad,b,h]};q=s.factor(beta[5].subs(only));p=[s.factor(v.subs(only)) for v in beta[6:]]
    Q=s.hessian(q,[x,y,z])/2;assert Q.det()!=0
    # Positive leading 2-by-2 principal block is not required; use exact LDL pivots.
    L,D=Q.LDLdecomposition(hermitian=False);pivots=[D[i,i] for i in range(3)];signature=[sum(bool(v>0) for v in pivots),sum(bool(v<0) for v in pivots)];assert signature==[2,1]
    patch1=_bezout_one([q.subs(x,1),(x*p[1]-y*p[0]).subs(x,1),(x*p[2]-z*p[0]).subs(x,1)],[y,z])
    patch2=_bezout_one([q.subs({x:0,y:1}),p[0].subs({x:0,y:1}),(y*p[2]-z*p[1]).subs({x:0,y:1})],[z])
    assert q.subs({x:0,y:0,z:1})==6
    # Extract pure mixed nonsinglet components with a polynomial of multiplication
    # by the sum of the two independent radial basis vectors.
    tensor={}
    for k,i,j,c in table:
        if k in indices and i in indices and j in indices:tensor[k,i,j]=s.Rational(c)
    def multiplication(left):
        M=s.zeros(9)
        for (k,i,j),c in tensor.items():
            M[indices.index(k),indices.index(j)]+=c*left[indices.index(i)]
            if i!=j:M[indices.index(k),indices.index(i)]+=c*left[indices.index(j)]
        return M
    radial=s.zeros(9,1);radial[0]=radial[2]=1;A=multiplication(radial);assert set(A.eigenvals())=={16,48,80,128}
    projector=s.eye(9)
    for eigen in [48,80,128]:projector=projector*(A-eigen*s.eye(9))/(16-eigen)
    expected=s.diag(0,0,0,0,0,1,1,1,1);assert projector==expected
    return {'ambient_quartic_indices':indices,'ambient_labels':labels,'ordinary_channel_regeneration_polynomial':str(q),
            'finite_cross_product':list(map(str,p)),'finite_regeneration_form':[[str(v) for v in row] for row in Q.tolist()],
            'exact_LDL_pivots':list(map(str,pivots)),'real_signature':signature,
            'mixed_nonsinglet_projector':'Product over e=48,80,128 of (L-e I)/(16-e), L=multiplication by radial_up+radial_down',
            'radial_multiplication_eigenvalues':[16,48,80,128],'exact_projector_identity':True,
            'projective_patch_x_nonzero':patch1,'projective_patch_x_zero_y_nonzero':patch2,'remaining_z_axis_regeneration':'6',
            'theorem':'Every real linear scalar-loop-closed subspace of this nine-operator adjoint algebra containing the two independent radial quartics and with ordinary_cross identically zero has all three finite cross coefficients identically zero.',
            'proof':'The radial multiplication projector extracts pure finite-cross vectors. Vanishing ordinary channel makes their span totally isotropic for a nondegenerate signature-(2,1) form, so it has dimension at most one. Closure then requires a nonzero null ray whose finite product is parallel to that ray. Exact Bezout identities exclude every projective patch.',
            'scope':'All rotated real linear restrictions under the stated independent-radial and pure-adjoint hypotheses. Nonlinear running varieties, correlated radial assumptions, additional singlets/mediators, or gauge/Yukawa/EFT cancellations are not excluded.'}
