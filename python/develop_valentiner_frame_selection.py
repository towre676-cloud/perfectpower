"""Allowed frame selectors, exact double-group orbits and nonlinear flatness.

No CKM targets. Canonical isolated link sector; scalar quartics are EFT
interactions, not a claimed supersymmetric gauge completion.
"""
from functools import lru_cache
from itertools import product
from math import factorial, prod
from fractions import Fraction as Q
from pathlib import Path
import json
import numpy as np
import sympy as s
from sympy.polys.matrices import DomainMatrix
from develop_valentiner_diagonal_vacua import tensor_data, full_diagonal_derivatives, determinant_hessians, X, soft_mass_certificate
from develop_valentiner_frames import generators, group_closure, product as fp, conjugate, numeric
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/m22_interactions/valentiner_frame_selection.json'


def compositions(n,k):
    if k==1:
        yield (n,);return
    for i in range(n+1):
        for tail in compositions(n-i,k-1):yield (i,)+tail


@lru_cache(None)
def full_sextic_polynomial():
    field,tensor,bar=tensor_data();v=s.symbols('k:9');terms={}
    for m in compositions(6,9):
        rows=tuple(sum(m[3*i+j] for j in range(3)) for i in range(3))
        cols=tuple(sum(m[3*i+j] for i in range(3)) for j in range(3))
        coefficient=bar.get(rows,field.zero)*tensor.get(cols,field.zero)*field.convert(factorial(6)//prod(factorial(n) for n in m))
        if coefficient:terms[m]=coefficient
    result=s.Poly.from_dict(terms,v,domain=field)
    assert len(terms)==252
    return result


@lru_cache(None)
def nonlinear_profile():
    field,_,_=tensor_data();P=full_sextic_polynomial();v=P.gens
    omega=(-1+s.I*s.sqrt(3))/2;point=(1,omega,omega**2)
    _,hessian=full_diagonal_derivatives();Hd,_=determinant_hessians()
    reduce=lambda z:field.to_sympy(field.from_sympy(z))
    H=(hessian-5*Hd).subs(dict(zip(X,point))).applyfunc(reduce)
    null=[]
    for ids in ((1,3),(2,6),(5,7)):
        block=H.extract(ids,ids);n=s.Matrix([-block[0,1]/block[0,0],1]).applyfunc(reduce)
        vector=s.zeros(9,1)
        for i,value in zip(ids,n):vector[i]=value
        assert (H*vector).applyfunc(reduce)==s.zeros(9,1)
        null.append(vector)
    u=s.symbols('u:3');t=s.symbols('t');massive=(0,4,8,1,2,5)
    base=s.Matrix([1,0,0,0,omega,0,0,0,omega**2])
    k=base+t*sum((a*b for a,b in zip(u,null)),s.zeros(9,1))
    WP=P-s.Poly(5*s.Matrix(3,3,v).det(),v,domain=field)
    def trunc(poly,n):
        return s.Poly.from_dict({m:c for m,c in poly.rep.to_dict().items() if m[0]<=n},(t,*u),domain=field)
    def make_powers(values,order):
        powers={}
        for i,value in enumerate(values):
            powers[i,0]=s.Poly(1,t,*u,domain=field)
            for n in range(1,7):powers[i,n]=trunc(powers[i,n-1]*s.Poly(value,t,*u,domain=field),order)
        return powers
    def restrict(poly,powers,order):
        answer=s.Poly(0,t,*u,domain=field)
        for m,c in poly.rep.to_dict().items():
            term=s.Poly(field.to_sympy(c),t,*u,domain=field)
            for i,n in enumerate(m):
                if n:term=trunc(term*powers[i,n],order)
            answer+=term
        return answer
    def part(poly,degree):
        return s.Poly.from_dict({m[1:]:c for m,c in poly.rep.to_dict().items() if m[0]==degree},u,domain=field)
    powers=make_powers(k,6);raw=restrict(WP,powers,6)
    assert part(raw,3).is_zero
    Hm=H.extract(massive,massive)
    inverse=DomainMatrix.from_Matrix(Hm).convert_to(field).inv().to_Matrix()
    C=[part(restrict(WP.diff(v[i]),powers,2),2) for i in massive]
    y2=[]
    for i in range(6):
        displacement=s.Poly(0,*u,domain=field)
        for j in range(6):displacement-=C[j]*s.Poly(inverse[i,j],*u,domain=field)
        y2.append(displacement)
    values=list(k)
    for i,index in enumerate(massive):values[index]+=t*t*y2[i].as_expr()
    powers=make_powers(values,6);relaxed=restrict(WP,powers,6)
    assert all(part(relaxed,n).is_zero for n in (3,4,5))
    R=[part(restrict(WP.diff(v[i]),powers,3),3) for i in massive]
    eff6=part(relaxed,6)
    for i in range(6):
        for j in range(6):eff6-=R[i]*R[j]*s.Poly(inverse[i,j]/2,*u,domain=field)
    assert eff6.is_zero
    result={'benchmark':'normalized a=-5,b=1,c=0; K0=diag(1,omega,omega^2)',
            'full_sextic_monomials':len(P.terms()),'null_vectors':[[str(z) for z in n] for n in null],
            'massive_coordinate_indices':list(massive),'massive_Hessian_inverse':[[str(z) for z in row] for row in inverse.tolist()],
            'quadratic_massive_displacements':[str(z.as_expr()) for z in y2],
            'cubic_massive_residuals':[str(z.as_expr()) for z in R],
            'raw_null_superpotential_quartic':str(part(raw,4).as_expr()),
            'effective_superpotential_degrees_3_4_5':['0','0','0'],
            'effective_superpotential_degree_6':str(eff6.as_expr()),
            'first_possible_effective_F_energy_degree':12,
            'scope':'Holomorphic implicit elimination of six massive coordinates. Canonical light metric must be retained when interpreting the first nonzero effective superpotential as energy.'}
    return result


@lru_cache(None)
def orbit_census():
    G=group_closure(generators())[0]
    keys=[tuple(conjugate(tuple(Q(n,d) for n in row)) for row in entries) for d,entries in G]
    lookup=set(keys);one=(Q(1),Q(0),Q(0),Q(0));omega=(Q(0),Q(0),Q(1),Q(0));diag=(one,omega,fp(omega,omega))
    distinct=[];axis=[]
    for index,M in enumerate(keys):
        image=tuple(fp(fp(diag[i],M[3*i+j]),conjugate(diag[j])) for i in range(3) for j in range(3))
        if image in lookup:distinct.append(index)
        if all(M[3*i+j]==(0,0,0,0) for i,j in ((0,2),(1,2),(2,0),(2,1))):axis.append(index)
    assert len(axis)==24 and len(distinct)==36
    counts={'group':1080,'nonunitary_q_plus':len(G)**2//len(axis),'nonunitary_q_minus':len(G)**2//len(axis),'massless_unitary':len(G)**2//len(distinct)}
    assert sum(counts.values())==130680
    monomial=[]
    for M in keys:
        support=[[j for j in range(3) if M[3*i+j]!=(0,0,0,0)] for i in range(3)]
        if all(len(row)==1 for row in support):monomial.append((tuple(row[0] for row in support),tuple(M[3*i+row[0]] for i,row in enumerate(support))))
    diagonal_sets={name:set() for name in ('group','distinct','nonunitary')}
    for permutation,left in monomial:
        for right_permutation,right in monomial:
            if permutation!=right_permutation:continue
            phases=tuple(fp(left[i],conjugate(right[i])) for i in range(3))
            diagonal_sets['group'].add(phases)
            diagonal_sets['distinct'].add(tuple(fp(phases[i],diag[permutation[i]]) for i in range(3)))
            diagonal_sets['nonunitary'].add(tuple((phases[i],permutation[i]==2) for i in range(3)))
    diagonal_counts={name:len(rows) for name,rows in diagonal_sets.items()}
    assert diagonal_counts=={'group':12,'distinct':24,'nonunitary':36}
    return {'group_order':len(G),'action':'K -> hL K hRdagger, hL,hR in conjugate(3.A6)',
            'nonunitary_stabilizer_indices':axis,'massless_stabilizer_indices':distinct,
            'stabilizer_orders':{'group':1080,'nonunitary':24,'massless':36},
            'orbit_sizes':counts,'monomial_subgroup_order':len(monomial),'diagonal_intersections':diagonal_counts,'certified_nonzero_vacua':sum(counts.values()),
            'certified_vacua_including_origin':130681,'certified_off_diagonal_vacua':130572,
            'strictly_stable_nonzero_vacua_at_benchmark':98280,
            'disjointness_invariant':'det K = -1/32, -(11+i sqrt(135))/64, -(11-i sqrt(135))/64, -1/5',
            'scope':'Exact orbit census and lower bound for the full vacuum set, not a complete classification of all F-flat matrices.'}


def invariant_selection():
    norms=soft_mass_certificate()['numeric_squared_Frobenius_norms']
    cubic={name:s.sympify(expr) for name,expr in soft_mass_certificate()['exact_cubed_squared_Frobenius_norms'].items()}
    # Rational intervals certify cube-root comparisons, including the algebraic
    # nonunitary norm, without treating floating-point energies as proofs.
    bounds={'equal_squares':(Q(297637697,10**9),Q(297637698,10**9)),
            'distinct_squares':(Q(1025985568,10**9),Q(1025985569,10**9)),
            'two_equal_squares':(Q(1219900741,10**9),Q(1219900742,10**9))}
    sqrt_lo=Q(3162277660168379,10**15);sqrt_hi=Q(3162277660168380,10**15)
    assert sqrt_lo**2<10<sqrt_hi**2
    for name,(lo,hi) in bounds.items():
        expr=cubic[name]
        low=expr.subs(s.sqrt(10),s.Rational(sqrt_lo));high=expr.subs(s.sqrt(10),s.Rational(sqrt_hi))
        assert s.Rational(lo)**3<low and high<s.Rational(hi)**3
    assert bounds['equal_squares'][0]>Q(1,4)
    assert bounds['distinct_squares'][1]<Q(8,5)
    assert bounds['two_equal_squares'][1]<Q(11,8)
    det={'equal_squares':s.Rational(-1,32),'distinct_squares':s.Rational(-1,5),'two_equal_squares':s.Rational(-11,64)}
    energies={name:-norms[name]-8*float(value) for name,value in det.items()}
    n0=norms['equal_squares'];lower=max((norms['distinct_squares']-n0)/(1/5-1/32),(norms['two_equal_squares']-n0)/(11/64-1/32));upper=32*n0
    census=json.loads((ROOT/'receipts/m22_interactions/valentiner_link.json').read_text())['bifundamental_bidegree_dimensions']
    assert census['1,1']==1 and census['3,0']==1 and census['2,2']==2
    return {'complete_CP_even_nonconstant_scalar_basis_through_degree_4':['N','Re det K','N^2','Tr((Kdagger K)^2)'],
            'N_definition':'Tr Kdagger K = squared Frobenius norm',
            'benchmark':'a=b=1,c=0','exact_norm_intervals':{k:[str(a),str(b)] for k,(a,b) in bounds.items()},
            'determinant_real_parts':{k:str(v) for k,v in det.items()},
            'soft_example':'delta V=epsilon*(-N-8 Re det K), epsilon positive and sufficiently small',
            'soft_example_first_order_energies':energies,'origin_first_order_energy':0,
            'soft_open_interval_t_numeric':[lower,upper],
            'soft_open_interval_t_exact':'max((Nd-Ng)/(1/5-1/32),(Nn-Ng)/(11/64-1/32)) < t < 32 Ng',
            'soft_scope':'Group orbit strictly favored at first order among all four certified orbits and the origin; not a global theorem for the soft-only perturbed full action.',
            'global_quartic_selector':'VF+lambda*(N-3*v^2)^2+eta*G; G=Tr(A-N I/3)^2; A=Kdagger K',
            'global_theorem_assumptions':'a real nonzero; b*c>0 real; lambda,eta>0; v^3=|a/(32*b+2*c)|',
            'unitary_Cauchy_Schwarz_bound':'|I6bar(K)|<=16*v^6',
            'Euler_phase_identity':'|I6bar(K)|^2/v^12 =256+2*t*(16+t)*(1-cos(delta)); t=c/b, det K=D0*exp(i delta)',
            'global_zero_set':'K=r U; r^3=-a/(32b+2c); U in SU(3), Tbar(U)=Tbar',
            'stabilizer_Lie_norm_identity':'||d Tbar(A)||^2=72 ||A||F^2 for traceless anti-Hermitian A',
            'global_zero_set_is_finite':True,'known_group_minima':1080,
            'global_scope':'All global minima of this calibrated isolated scalar EFT are characterized by the finite unitary tensor stabilizer. Its full order is not equated with 1080 without a separate stabilizer classification.',
            'quartic_gauge_warning':'G is a symmetry-allowed balanced quartic. Formal moment-map equality does not gauge the fixed finite-group sextic consistently. N^2 and G are not asserted to be soft SUSY-breaking operators.',
            'CP_or_CKM_prediction':False}



def stabilizer_lie_certificate():
    field,tensor,bar=tensor_data();z=s.symbols('z:3')
    terms={m:value*field.convert(factorial(6)//prod(factorial(n) for n in m)) for m,value in bar.items()}
    polynomial=s.Poly.from_dict(terms,z,domain=field).as_expr()
    generators=[]
    for i,j in ((0,1),(0,2),(1,2)):
        A=s.zeros(3);A[i,j]=1;A[j,i]=-1;generators.append(A)
        A=s.zeros(3);A[i,j]=A[j,i]=s.I*s.sqrt(3);generators.append(A)
    generators.extend([s.I*s.sqrt(3)*s.diag(1,-1,0),s.I*s.sqrt(3)*s.diag(1,1,-2)])
    derivatives=[]
    for A in generators:
        Az=A*s.Matrix(z)
        derivatives.append(s.Poly(sum(s.diff(polynomial,z[i])*Az[i] for i in range(3)),z,domain=field).rep.to_dict())
    gram=[]
    for i,A in enumerate(generators):
        row=[]
        for j,B in enumerate(generators):
            value=field.zero
            for m,c in derivatives[i].items():
                mult=factorial(6)//prod(factorial(n) for n in m)
                value+=field.from_sympy(s.conjugate(field.to_sympy(c)))*derivatives[j].get(m,field.zero)/field.convert(mult)
            expected=field.from_sympy(72*s.trace(A.conjugate().T*B))
            assert value==expected
            row.append(str(field.to_sympy(value)))
        gram.append(row)
    return {'exact_Gram_comparisons':64,'Gram':gram,'rank':8,'compact_SU3_stabilizer_is_finite':True}

def build():
    return {'stabilizer_Lie':stabilizer_lie_certificate(),'selection':invariant_selection(),'orbits':orbit_census(),'nonlinear_massless_branch':nonlinear_profile()}


if __name__=='__main__':
    data=build();OUT.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    print(OUT)
