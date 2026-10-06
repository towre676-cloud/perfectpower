"""Polarized de Rham pairing and bounded filtered horizontal searches.

Filtration compatibility is checked algebraically. Betti rationality, complex
conjugation, algebraic correspondences and Jacobian factors are not inferred.
"""
from fractions import Fraction as Q
from . import field_polynomials as F, polyalg as P, exact_linear as E
from .rational_functions import RationalFunction as RF, AlgebraBudget
from .curve_families import encode_matrix
from .core import mul


def de_rham_pairing(family):
    """Residue of a local primitive times a differential at infinity."""
    budget=AlgebraBudget(**family.limits);f=[RF.parse(v,budget) for v in family.f];m=len(f)-1;n=family.dimension;zero=f[0].coerce(0);one=zero.coerce(1)
    if m%2!=1 or family.genus!=(m-1)//2:raise ValueError('monic odd-degree power basis required')
    length=4*family.genus+2;w=[zero]*(length+1);w[0]=one
    for i,a in enumerate(f[:-1]):
        k=2*(m-i)
        if k<=length:w[k]=a
    b=[one]
    for k in range(1,length+1):b.append(-sum(((k-j+Q(j,2))*w[j]*b[k-j] for j in range(1,k+1)),zero)/k)
    forms=[{m-2*i-3+k:-2*a for k,a in enumerate(b) if a} for i in range(n)]
    pairing=[]
    for left in forms:
        row=[]
        for right in forms:
            row.append(sum((c*right.get(-2-k,zero)/(k+1) for k,c in left.items() if k!=-1),zero))
        pairing.append(row)
    if any(pairing[i][j]!=-pairing[j][i] for i in range(n) for j in range(n)) or F.matrix_rank(pairing)!=n:raise AssertionError('de Rham residue pairing not symplectic')
    a=[[RF.parse(v,budget) for v in row] for row in family.connection];aj=F.matrix_product(a,pairing);jat=F.matrix_product(pairing,list(map(list,zip(*a))))
    if any(pairing[i][j].derivative()!=aj[i][j]+jat[i][j] for i in range(n) for j in range(n)):raise AssertionError('pairing is not horizontal')
    return pairing


def projector_check(family,matrix):
    n=family.dimension;budget=AlgebraBudget(**family.limits)
    if not isinstance(matrix,list) or len(matrix)!=n or any(len(row)!=n for row in matrix):raise ValueError('square projector in the current de Rham basis required')
    p=[[RF.parse(v,budget) for v in row] for row in matrix];a=[[RF.parse(v,budget) for v in row] for row in family.connection];j=de_rham_pairing(family)
    pp=F.matrix_product(p,p);pa=F.matrix_product(p,a);ap=F.matrix_product(a,p)
    pj=F.matrix_product(p,j);jpt=F.matrix_product(j,list(map(list,zip(*p))))
    return dict(idempotent=pp==p,horizontal=not any(p[i][k].derivative()+pa[i][k]-ap[i][k] for i in range(n) for k in range(n)),
        holomorphic_filtration_preserved=not any(p[i][k] for i in range(family.genus) for k in range(family.genus,n)),
        polarization_self_adjoint=pj==jpt,rank=F.matrix_rank(p),matrix=encode_matrix(p),
        scope='de Rham horizontality, F^1 preservation and residue-pairing self-adjointness; no rational Betti lattice, conjugate filtration, algebraic correspondence or Jacobian decomposition certified')


def search_horizontal_projectors(family,degree=0,denominator=None,candidate_limit=128):
    if type(degree) is not int or not 0<=degree<=2:raise ValueError('numerator ansatz degree zero through two required')
    if type(candidate_limit) is not int or not 1<=candidate_limit<=256:raise ValueError('candidate limit one through 256 required')
    budget=AlgebraBudget(**family.limits);n=family.dimension;g=family.genus;zero=RF([0],budget=budget)
    d=RF(denominator or [1],budget=budget)
    if not d:raise ValueError('nonzero polynomial ansatz denominator required')
    a=[[RF.parse(v,budget) for v in row] for row in family.connection];j=de_rham_pairing(family)
    indices=[(r,c,k) for r in range(n) for c in range(n) if not (r<g and c>=g) for k in range(degree+1)]
    equations=[[] for _ in range(2*n*n)]
    for r,c,k in indices:
        q=RF([0]*k+[1],budget=budget)/d;p=[[zero for _ in range(n)] for _ in range(n)];p[r][c]=q
        pa=F.matrix_product(p,a);ap=F.matrix_product(a,p);pj=F.matrix_product(p,j);jpt=F.matrix_product(j,list(map(list,zip(*p))))
        values=[(q.derivative() if (i,l)==(r,c) else zero)+pa[i][l]-ap[i][l] for i in range(n) for l in range(n)]
        values.extend(pj[i][l]-jpt[i][l] for i in range(n) for l in range(n))
        for row,value in zip(equations,values):row.append(value)
    rows=[]
    for equation in equations:
        if not any(equation):continue
        common=P.ONE
        for v in equation:common=mul(common,P.exact_div(v.d,P.gcd_poly(common,v.d)));budget.check(common)
        polys=[mul(v.n,P.exact_div(common,v.d)) for v in equation]
        for k in range(max(len(p) for p in polys)):
            row=[p[k] if k<len(p) else Q(0) for p in polys]
            if any(row):rows.append(row)
    vectors=E.kernel(rows) if rows else E.identity(len(indices))
    basis=[]
    for vector in vectors:
        p=[[zero for _ in range(n)] for _ in range(n)]
        for v,(r,c,k) in zip(vector,indices):p[r][c]=p[r][c]+v*RF([0]*k+[1],budget=budget)/d
        check=projector_check(family,encode_matrix(p))
        if not all(check[key] for key in ('horizontal','holomorphic_filtration_preserved','polarization_self_adjoint')):raise AssertionError('horizontal ansatz replay failed')
        basis.append(p)
    candidates=[]
    # Finite declared list: basis elements, complements and pair sums. This is
    # a search for idempotents in the linear space, not a nonlinear census.
    identity=[[zero.coerce(int(i==k)) for k in range(n)] for i in range(n)]
    for p in basis:
        candidates.extend([p,[[identity[i][k]-p[i][k] for k in range(n)] for i in range(n)]])
    for i,p in enumerate(basis):
        for q in basis[i+1:]:candidates.append([[p[r][c]+q[r][c] for c in range(n)] for r in range(n)])
    found=[];seen=set()
    from .catalogue import encoded
    for p in candidates[:candidate_limit]:
        check=projector_check(family,encode_matrix(p));key=encoded(check['matrix'])
        if check['idempotent'] and 0<check['rank']<n and key not in seen:seen.add(key);found.append(check)
    return dict(schema='pp-filtered-horizontal-search/1',ansatz_degree=degree,denominator=d.packet(),
        linear_space_dimension=len(basis),linear_space_basis=[encode_matrix(p) for p in basis],
        linear_ansatz_complete=True,candidates_tested=min(len(candidates),candidate_limit),candidate_list_truncated=len(candidates)>candidate_limit,
        projectors=found,pairing=encode_matrix(j),pairing_identity_checked=True,algebra_work=budget.work,
        scope='complete filtered polarized horizontal endomorphism space in the bounded numerator/shared-denominator ansatz; only the declared finite idempotent candidates tested; no Jacobian decomposition inferred')
