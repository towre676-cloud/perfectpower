"""Complete prime-preimage generators for finitely generated rational subgroups.

For p=2,3,5 or 7 enumerate coefficient lines in F_p^r. Complete rational division
fibres identify the linear relation space in E(Q)/pE(Q). Its RREF pivots give
exact replacement generators; the complete rational p-kernel is retained.
No assumption of independence, rank completeness or torsion classification.
"""
from itertools import product
from .elliptic_arithmetic import encode_point,root_budget
from .elliptic_division import ordered
from .elliptic_prime_division import rational_prime_division
from .elliptic_presentation import coefficient_presentation
from .elliptic_certificate_verifier import CheckBudget
from .divisor_square import WorkLimit


def parameters(prime,points):
    if type(prime) is not int or prime not in (2,3,5,7):raise ValueError('prime 2, 3, 5 or 7 required')
    if not isinstance(points,(list,tuple)) or len(points)>4:raise ValueError('at most four subgroup generators')


def lines(prime,width):
    return [v for v in product(range(prime),repeat=width) if any(v) and next(x for x in v if x)==1]


def linear_combination(E,points,coefficients):
    out=None
    for p,c in zip(points,coefficients):out=E.add(out,E.mul(p,c))
    return out


def row_basis(rows,prime,width):
    a=[list(v) for v in rows];i=0
    for j in range(width):
        pivot=next((k for k in range(i,len(a)) if a[k][j]%prime),None)
        if pivot is None:continue
        a[i],a[pivot]=a[pivot],a[i];inv=pow(a[i][j],-1,prime)
        a[i]=[v*inv%prime for v in a[i]]
        for k in range(len(a)):
            if k!=i:
                c=a[k][j];a[k]=[(x-c*y)%prime for x,y in zip(a[k],a[i])]
        i+=1
    return a[:i]


def subgroup_preimage(E,points,prime=2,node_limit=100000):
    parameters(prime,points);root_budget(node_limit)
    source=[E.checked(p) for p in points];r=len(source)
    divide=(E.rational_halves if prime==2 else E.rational_thirds if prime==3
            else lambda target,limit:rational_prime_division(E,target,prime,limit,local_obstructions=True))
    kernel=divide(None,node_limit);used=kernel['root_nodes'];packets=[];relations=[]
    for vector in lines(prime,r):
        if used>=node_limit:raise WorkLimit('shared subgroup division budget exhausted')
        target=linear_combination(E,source,vector)
        fibre=divide(target,node_limit-used);used+=fibre['root_nodes']
        packets.append(dict(coefficients=list(vector),fibre=fibre))
        if fibre['points']:relations.append(vector)
    basis=row_basis(relations,prime,r)
    replacements=list(source);equations=[]
    lookup={tuple(row['coefficients']):row['fibre'] for row in packets}
    for vector in basis:
        pivot=next(i for i,v in enumerate(vector) if v)
        fibre=lookup[tuple(vector)];anchor=E.checked(fibre['points'][0])
        replacements[pivot]=anchor
        equations.append(dict(pivot=pivot,coefficients=vector,preimage=encode_point(anchor)))
    kernel_points=[E.checked(h) for h in kernel['points']]
    generators=ordered([*replacements,*kernel_points]);generators=[p for p in generators if p is not None]
    result=dict(schema='pp-elliptic-subgroup-preimage/2',curve=E.specification,
        source_points=[encode_point(h) for h in source],prime=prime,
        kernel_fibre=kernel,projective_fibres=packets,relation_basis=basis,
        relation_dimension=len(basis),replacement_equations=equations,
        replacement_points=[encode_point(h) for h in replacements],
        generators=[encode_point(h) for h in generators],complete=True,
        coefficient_presentation=coefficient_presentation(prime,basis,r),
        scope='complete generators for the rational prime-preimage of the supplied subgroup',
        complete_mordell_weil_group=False,execution_verified=False,
        node_limit=node_limit,root_nodes=used)
    CheckBudget(2000000).packet(result)
    return result
