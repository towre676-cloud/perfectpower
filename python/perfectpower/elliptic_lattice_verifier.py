"""Replay lattice normal forms with independent exact matrix arithmetic.

No Hermite/Smith producer, elimination, membership search or root discovery
is invoked. Existing prime-fibre replay uses the original-model b-invariants.
"""
from fractions import Fraction
from itertools import product
from .elliptic_certificate_verifier import CheckBudget,fields,exact_int,model,checked_point
from .elliptic_subgroup_verifier import _check
from .elliptic_saturation_verifier import verify_saturation,combination
from .divisor_square import WorkLimit


def matrix(A,n):
    return (type(A) is list and len(A)==n and
            all(type(row) is list and len(row)==n and
                all(type(x) is int and -256<=x<=256 for x in row) for row in A))


def multiply(A,B):
    n=len(A);return [[sum(A[i][k]*B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]


def determinant(A):
    n=len(A);a=[[Fraction(x) for x in row] for row in A];value=Fraction(1)
    for j in range(n):
        k=next((k for k in range(j,n) if a[k][j]),None)
        if k is None:return 0
        if k!=j:a[k],a[j]=a[j],a[k];value=-value
        pivot=a[j][j];value*=pivot
        for i in range(j+1,n):
            c=a[i][j]/pivot
            for k in range(j,n):a[i][k]-=c*a[j][k]
    assert value.denominator==1
    return value.numerator


def _lattice(preimage,lattice,budget):
    fields(lattice,'row_hermite smith_left smith_right smith_diagonal coefficient_lattice_index residue_relation_cardinality source_inclusion')
    r=len(preimage['source_points']);p=preimage['prime'];R=preimage['relation_basis'];d=len(R)
    H,U,V,I=[lattice[k] for k in ('row_hermite','smith_left','smith_right','source_inclusion')]
    if not all(matrix(a,r) for a in (H,U,V,I)):return False
    diag=lattice['smith_diagonal']
    if type(diag) is not list or any(type(x) is not int for x in diag) or diag!=[1]*d+[p]*(r-d):return False
    index=exact_int(lattice['coefficient_lattice_index'],1,p**r)
    cardinality=exact_int(lattice['residue_relation_cardinality'],1,p**r)
    if index!=p**(r-d) or cardinality!=p**d:return False
    if determinant(H)!=index or abs(determinant(U))!=1 or abs(determinant(V))!=1:return False
    if multiply(multiply(U,H),V)!=[[diag[i]*int(i==j) for j in range(r)] for i in range(r)]:return False
    # Upper triangular row Hermite convention: positive pivots, reduced above.
    for i in range(r):
        if H[i][i] not in (1,p) or any(H[i][j] for j in range(i)):return False
        if any(not 0<=H[j][i]<H[i][i] for j in range(i)):return False
    relation_span={tuple(sum(c*row[j] for c,row in zip(cs,R))%p for j in range(r))
                   for cs in product(range(p),repeat=d)}
    if len(relation_span)!=cardinality:return False
    if any(tuple(x%p for x in row) not in relation_span for row in H):return False
    # H lies in the target lattice and has its independently determined index.
    # Verify actual point lifts and every source containment relation as well.
    E=model(preimage['curve']);source=[checked_point(E,x) for x in preimage['source_points']]
    replacements=[checked_point(E,x) for x in preimage['replacement_points']]
    for j,row in enumerate(H):
        budget.charge(r*p)
        if E.mul(replacements[j],p)!=combination(E,source,row,budget):return False
    for point,row in zip(source,I):
        if combination(E,replacements,row,budget)!=point:return False
    return True


def verify_subgroup_presentation(cert,*,work_limit=4000000,node_limit=100000):
    try:
        budget=CheckBudget(work_limit);budget.packet(cert)
        fields(cert,'schema preimage lattice actual_subgroup_index scope complete_mordell_weil_group execution_verified')
        if (cert['schema']!='pp-elliptic-prime-preimage-presentation/1' or cert['actual_subgroup_index'] is not None or
            cert['scope']!='coefficient lattice normal forms and complete rational prime-preimage generators' or
            cert['complete_mordell_weil_group'] is not False or cert['execution_verified'] is not False):return False
        exact_int(node_limit,1,100000)
        return _check(cert['preimage'],budget,node_limit) and _lattice(cert['preimage'],cert['lattice'],budget)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,WorkLimit):return False


def verify_saturation_presentation(cert,*,work_limit=8000000,node_limit=100000):
    try:
        budget=CheckBudget(work_limit);budget.packet(cert)
        fields(cert,'schema saturation stage_lattices actual_subgroup_indices complete_mordell_weil_group execution_verified')
        if (cert['schema']!='pp-elliptic-prime-saturation-presentation/1' or cert['actual_subgroup_indices'] is not None or
            cert['complete_mordell_weil_group'] is not False or cert['execution_verified'] is not False):return False
        if not verify_saturation(cert['saturation'],work_limit=work_limit,node_limit=node_limit):return False
        lattices=cert['stage_lattices'];stages=cert['saturation']['stages']
        return (type(lattices) is list and len(lattices)==len(stages) and
                all(_lattice(s['preimage'],a,budget) for s,a in zip(stages,lattices)))
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,WorkLimit):return False


def verify_subgroup_index(cert,*,work_limit=8000000,node_limit=100000):
    try:
        from .elliptic_certificate_verifier import verify_independence
        budget=CheckBudget(work_limit);budget.packet(cert)
        fields(cert,'schema presentation basis independence source_coordinates replacement_coordinates actual_subgroup_index complete_mordell_weil_group execution_verified')
        if (cert['schema']!='pp-elliptic-subgroup-index/1' or cert['complete_mordell_weil_group'] is not False or cert['execution_verified'] is not False):return False
        c=cert['presentation']
        if not verify_subgroup_presentation(c,work_limit=work_limit,node_limit=node_limit):return False
        core=c['preimage'];E=model(core['curve']);r=len(core['source_points'])
        if not 1<=r<=4 or type(cert['basis']) is not list or len(cert['basis'])!=r:return False
        basis=[checked_point(E,p) for p in cert['basis']]
        proof=cert['independence']
        if (type(proof) is not dict or proof.get('curve')!=core['curve'] or proof.get('original_points')!=cert['basis'] or
            proof.get('independent') is not True or not verify_independence(proof,work_limit=work_limit,node_limit=node_limit)):return False
        if core['kernel_fibre']['points']!=[None]:return False
        S,T=cert['source_coordinates'],cert['replacement_coordinates']
        if not matrix(S,r) or not matrix(T,r):return False
        for name,A in [('source_points',S),('replacement_points',T)]:
            points=[checked_point(E,p) for p in core[name]]
            if any(combination(E,basis,row,budget)!=p for p,row in zip(points,A)):return False
        a,b=abs(determinant(S)),abs(determinant(T))
        return bool(a and b and a%b==0 and exact_int(cert['actual_subgroup_index'],1,2**64)==a//b)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,WorkLimit):return False
